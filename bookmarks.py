#!/usr/bin/env python3
"""Zakładki z tagami i wyszukiwarką.

  zakladki          – okno wyszukiwania
  zakladki --add    – dodaj zakładkę (adres ze schowka)

Baza: $ZAKLADKI_DB, albo linia "db = ..." w ~/.config/zakladki/config,
albo domyślnie ~/.local/share/bookmark-search/bookmarks.db.
"""

import argparse
import html
import os
import re
import shutil
import sqlite3
import subprocess
import sys
import tempfile
import threading
import time
import unicodedata
import urllib.request
import zlib
from html.parser import HTMLParser
from pathlib import Path

from PySide6.QtCore import (
    QAbstractTableModel, QFileSystemWatcher, QModelIndex, QObject, Qt, QTimer, QUrl, Signal,
)
from PySide6.QtGui import QAction, QClipboard, QDesktopServices, QGuiApplication, QKeySequence
from PySide6.QtWidgets import (
    QAbstractItemView, QApplication, QCompleter, QDialog, QDialogButtonBox,
    QFileDialog, QFormLayout, QHeaderView, QInputDialog, QLabel, QLineEdit,
    QListWidget, QListWidgetItem, QMainWindow, QMenu, QMessageBox, QSplitter,
    QTableView, QVBoxLayout, QWidget,
)

DATA_DIR = Path(os.environ.get("XDG_DATA_HOME", Path.home() / ".local/share")) / "bookmark-search"
CONFIG_FILE = Path(os.environ.get("XDG_CONFIG_HOME", Path.home() / ".config")) / "zakladki/config"
CONFLICTS_DIR = DATA_DIR / "scalone-konflikty"
RESULT_LIMIT = 5000


# ----------------------------------------------------------------------- tekst

_FOLD_EXTRA = str.maketrans({"ł": "l", "Ł": "L", "ø": "o", "Ø": "O", "đ": "d", "Đ": "D", "ß": "ss"})


def fold(s):
    """Małe litery bez znaków diakrytycznych: 'Zażółć' -> 'zazolc'."""
    if not s:
        return ""
    s = unicodedata.normalize("NFKD", s.translate(_FOLD_EXTRA))
    return "".join(c for c in s if not unicodedata.combining(c)).lower()


def fts_query(text: str) -> str:
    # każde słowo jako prefiks, wszystkie muszą wystąpić (AND)
    words = re.findall(r"\w+", fold(text), re.UNICODE)
    return " ".join(f'"{w}"*' for w in words)


def parse_tags(text) -> list[str]:
    parts = text.split(",") if isinstance(text, str) else text
    out = []
    for t in parts:
        t = " ".join(t.split()).lower()
        if t and t not in out:
            out.append(t)
    return out


# --------------------------------------------------------------------------- baza

def db_path() -> Path:
    env = os.environ.get("ZAKLADKI_DB")
    if env:
        return Path(env).expanduser()
    if CONFIG_FILE.exists():
        for line in CONFIG_FILE.read_text().splitlines():
            key, _, value = line.partition("=")
            if key.strip() == "db" and value.strip():
                return Path(value.strip()).expanduser()
    return DATA_DIR / "bookmarks.db"


def file_id(path: Path):
    try:
        st = path.stat()
    except FileNotFoundError:
        return None
    return st.st_dev, st.st_ino


def read_store_file(path: Path):
    """Zakładki z innego pliku bazy (np. kopii konfliktu Syncthinga)."""
    db = sqlite3.connect(f"file:{path}?mode=ro", uri=True)
    try:
        return [{"url": url, "title": title, "added": added, "tags": (tags or "").split("\x1f")}
                for url, title, added, tags in db.execute("""
                    SELECT b.url, b.title, b.added,
                           (SELECT group_concat(tag, char(31)) FROM tags WHERE bookmark_id = b.id)
                    FROM bookmarks b""")]
    finally:
        db.close()


class Store:
    def __init__(self, path: Path):
        self.path = path
        path.parent.mkdir(parents=True, exist_ok=True)
        self._move_old_schema(path)
        self._conn = None
        self._open()
        self.merge_conflicts()

    def _open(self):
        if self._conn:
            self._conn.close()
        self._conn = sqlite3.connect(self.path)
        self._file_id = file_id(self.path)
        self._conn.execute("PRAGMA foreign_keys = ON")
        self._conn.executescript("""
            CREATE TABLE IF NOT EXISTS bookmarks (
                id    INTEGER PRIMARY KEY,
                url   TEXT NOT NULL UNIQUE,
                title TEXT NOT NULL DEFAULT '',
                added INTEGER NOT NULL DEFAULT 0
            );
            CREATE TABLE IF NOT EXISTS tags (
                bookmark_id INTEGER NOT NULL REFERENCES bookmarks(id) ON DELETE CASCADE,
                tag         TEXT NOT NULL,
                PRIMARY KEY (bookmark_id, tag)
            );
            CREATE INDEX IF NOT EXISTS tags_tag ON tags(tag);
            -- indeks trzyma tekst po fold(), więc "zazolc" znajdzie "Zażółć"
            CREATE VIRTUAL TABLE IF NOT EXISTS bookmarks_fts USING fts5(
                title, url, tags, tokenize='unicode61'
            );
        """)

    @property
    def db(self):
        # Syncthing nie nadpisuje pliku, tylko podmienia go na nowy (inny i-węzeł).
        # Stare połączenie czytałoby wtedy i zapisywało skasowaną kopię.
        if not self._conn.in_transaction:
            fid = file_id(self.path)
            if fid and fid != self._file_id:
                self._open()
        return self._conn

    def sync_from_disk(self) -> bool:
        """Otwiera podmieniony plik i scala konflikty. True, jeśli dane mogły się zmienić."""
        fid = file_id(self.path)
        reopened = bool(fid and fid != self._file_id)
        if reopened:
            self._open()
        return self.merge_conflicts() > 0 or reopened

    def merge_conflicts(self) -> int:
        """Dodaje zakładki z plików *.sync-conflict-* (zmiany z dwóch komputerów naraz),
        a same pliki przenosi do CONFLICTS_DIR."""
        added = 0
        for f in sorted(self.path.parent.glob(f"{self.path.stem}.sync-conflict-*{self.path.suffix}")):
            try:
                items = read_store_file(f)
            except sqlite3.Error:
                continue  # np. plik jeszcze się synchronizuje – spróbujemy później
            added += self.import_items(items)
            CONFLICTS_DIR.mkdir(parents=True, exist_ok=True)
            shutil.move(str(f), CONFLICTS_DIR / f.name)
        return added

    @staticmethod
    def _move_old_schema(path: Path):
        # pierwsza wersja miała kolumnę "folder" – odkładamy ją na bok
        if not path.exists():
            return
        db = sqlite3.connect(path)
        cols = [r[1] for r in db.execute("PRAGMA table_info(bookmarks)")]
        db.close()
        if "folder" in cols:
            path.rename(path.with_suffix(".db.old"))

    def _reindex(self, bid):
        title, url = self.db.execute("SELECT title, url FROM bookmarks WHERE id = ?", (bid,)).fetchone()
        tags = " ".join(self.tags_of(bid))
        self.db.execute("DELETE FROM bookmarks_fts WHERE rowid = ?", (bid,))
        self.db.execute("INSERT INTO bookmarks_fts(rowid, title, url, tags) VALUES (?, ?, ?, ?)",
                        (bid, fold(title), fold(url), fold(tags)))

    def tags_of(self, bid) -> list[str]:
        return [r[0] for r in self.db.execute(
            "SELECT tag FROM tags WHERE bookmark_id = ? ORDER BY tag", (bid,))]

    def get(self, bid):
        r = self.db.execute("SELECT id, url, title FROM bookmarks WHERE id = ?", (bid,)).fetchone()
        return (r[0], r[1], r[2], self.tags_of(r[0])) if r else None

    def find_url(self, url):
        r = self.db.execute("SELECT id FROM bookmarks WHERE url = ?", (url,)).fetchone()
        return self.get(r[0]) if r else None

    def save(self, url, title, tags, bid=None) -> int:
        """Nowa zakładka (bid=None) albo zmiana istniejącej. Tagi są zastępowane."""
        url, title = url.strip(), title.strip()
        with self.db:
            if bid is None:
                bid = self.db.execute("INSERT INTO bookmarks(url, title, added) VALUES (?, ?, ?)",
                                      (url, title, int(time.time()))).lastrowid
            else:
                self.db.execute("UPDATE bookmarks SET url = ?, title = ? WHERE id = ?", (url, title, bid))
                self.db.execute("DELETE FROM tags WHERE bookmark_id = ?", (bid,))
            self.db.executemany("INSERT INTO tags(bookmark_id, tag) VALUES (?, ?)",
                                [(bid, t) for t in parse_tags(tags)])
            self._reindex(bid)
        return bid

    def import_items(self, items) -> int:
        """Dodaje tylko nowe adresy; istniejącym dopisuje brakujące tagi.
        Tytułów zmienionych ręcznie nie rusza."""
        added = 0
        with self.db:
            for it in items:
                url = it["url"].strip()
                if not url:
                    continue
                row = self.db.execute("SELECT id FROM bookmarks WHERE url = ?", (url,)).fetchone()
                if row:
                    bid = row[0]
                else:
                    bid = self.db.execute("INSERT INTO bookmarks(url, title, added) VALUES (?, ?, ?)",
                                          (url, it.get("title") or url,
                                           int(it.get("added") or time.time()))).lastrowid
                    added += 1
                self.db.executemany("INSERT OR IGNORE INTO tags(bookmark_id, tag) VALUES (?, ?)",
                                    [(bid, t) for t in parse_tags(it.get("tags", []))])
                self._reindex(bid)
        return added

    def delete(self, ids):
        with self.db:
            for bid in ids:
                self.db.execute("DELETE FROM bookmarks WHERE id = ?", (bid,))
                self.db.execute("DELETE FROM bookmarks_fts WHERE rowid = ?", (bid,))

    def search(self, text: str, tags: list[str]):
        sql = """SELECT b.id, b.title, b.url,
                        (SELECT group_concat(tag, ', ') FROM
                            (SELECT tag FROM tags WHERE bookmark_id = b.id ORDER BY tag)),
                        b.added
                 FROM bookmarks b"""
        where, params, order = [], [], "b.added DESC"
        query = fts_query(text)
        if query:
            sql += " JOIN bookmarks_fts f ON f.rowid = b.id"
            where.append("bookmarks_fts MATCH ?")
            params.append(query)
            order = "bm25(bookmarks_fts, 10.0, 3.0, 5.0)"
        if tags:
            # zakładka musi mieć wszystkie zaznaczone tagi
            where.append(f"""b.id IN (SELECT bookmark_id FROM tags
                             WHERE tag IN ({",".join("?" * len(tags))})
                             GROUP BY bookmark_id HAVING count(*) = ?)""")
            params += [*tags, len(tags)]
        if where:
            sql += " WHERE " + " AND ".join(where)
        sql += f" ORDER BY {order} LIMIT {RESULT_LIMIT}"
        return self.db.execute(sql, params).fetchall()

    def all_tags(self):
        return self.db.execute(
            "SELECT tag, count(*) FROM tags GROUP BY tag ORDER BY tag").fetchall()

    def count(self) -> int:
        return self.db.execute("SELECT count(*) FROM bookmarks").fetchone()[0]


# ------------------------------------------------------------------- importery

FIREFOX_ROOTS = ("menu________", "toolbar_____", "unfiled_____", "mobile______")


def find_firefox_profiles():
    bases = [Path.home() / ".mozilla/firefox",
             Path.home() / "snap/firefox/common/.mozilla/firefox",
             Path.home() / ".var/app/org.mozilla.firefox/.mozilla/firefox"]
    found = [db for base in bases if base.is_dir() for db in base.glob("*/places.sqlite")]
    # najświeższy profil na początku
    return sorted(found, key=lambda p: p.stat().st_mtime, reverse=True)


def read_firefox(places: Path):
    """Zakładki z places.sqlite. Tagi Firefoksa i nazwy folderów stają się tagami."""
    # Firefox trzyma bazę zablokowaną, a świeże zmiany są w pliku -wal,
    # więc kopiujemy oba pliki i czytamy kopię.
    with tempfile.TemporaryDirectory() as tmp:
        dst = Path(tmp) / "places.sqlite"
        shutil.copy2(places, dst)
        for suffix in ("-wal", "-shm"):
            extra = places.with_name(places.name + suffix)
            if extra.exists():
                shutil.copy2(extra, dst.with_name(dst.name + suffix))
        db = sqlite3.connect(dst)
        try:
            nodes = {r[0]: r[1:] for r in db.execute(
                "SELECT id, parent, title, guid FROM moz_bookmarks")}
            tags_root = next((i for i, n in nodes.items() if n[2] == "tags________"), None)

            tags_by_place = {}
            if tags_root is not None:
                for title, fk in db.execute("""
                        SELECT t.title, b.fk FROM moz_bookmarks b
                        JOIN moz_bookmarks t ON b.parent = t.id
                        WHERE t.parent = ? AND b.type = 1""", (tags_root,)):
                    tags_by_place.setdefault(fk, []).append(title or "")

            def folder_names(folder_id):
                names = []
                while folder_id in nodes:
                    parent, title, guid = nodes[folder_id]
                    if parent == 0 or guid in FIREFOX_ROOTS:
                        break
                    names.append(title or "")
                    folder_id = parent
                return names

            items = []
            for parent, title, fk, added, url in db.execute("""
                    SELECT b.parent, b.title, b.fk, b.dateAdded, p.url
                    FROM moz_bookmarks b JOIN moz_places p ON b.fk = p.id
                    WHERE b.type = 1"""):
                if parent in nodes and nodes[parent][0] == tags_root:
                    continue  # wpisy w folderach tagów to nie osobne zakładki
                if url.startswith("place:"):
                    continue  # inteligentne zakładki / zapytania
                items.append({"url": url, "title": title or url,
                              "tags": tags_by_place.get(fk, []) + folder_names(parent),
                              "added": (added or 0) // 1_000_000})
            return items
        finally:
            db.close()


class NetscapeParser(HTMLParser):
    """Format eksportu HTML zakładek (Firefox, Chrome, ...). Foldery -> tagi."""

    ROOT_NAMES = {"bookmarks menu", "bookmarks toolbar", "other bookmarks", "bookmarks bar",
                  "menu zakładek", "pasek zakładek", "inne zakładki"}

    def __init__(self):
        super().__init__()
        self.items, self.stack = [], []
        self.pending_folder = None
        self.current = None
        self.in_h3 = False

    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
        if tag == "h3":
            self.in_h3, self.pending_folder = True, ""
        elif tag == "dl":
            self.stack.append(self.pending_folder or "")
            self.pending_folder = None
        elif tag == "a" and a.get("href"):
            folders = [f.strip() for f in self.stack
                       if f.strip() and f.strip().lower() not in self.ROOT_NAMES]
            self.current = {"url": a["href"], "title": "",
                            "tags": (a.get("tags") or "").split(",") + folders,
                            "added": int(a.get("add_date") or 0)}

    def handle_endtag(self, tag):
        if tag == "h3":
            self.in_h3 = False
        elif tag == "dl" and self.stack:
            self.stack.pop()
        elif tag == "a" and self.current:
            self.current["title"] = self.current["title"].strip() or self.current["url"]
            self.items.append(self.current)
            self.current = None

    def handle_data(self, data):
        if self.in_h3:
            self.pending_folder += data
        elif self.current is not None:
            self.current["title"] += data


def read_html(path: Path):
    p = NetscapeParser()
    p.feed(path.read_text(encoding="utf-8", errors="replace"))
    return p.items


# ------------------------------------------------------------ dodawanie / edycja

def looks_like_url(s: str) -> bool:
    return bool(re.match(r"^(https?|ftp|file)://\S+$|^www\.\S+$", s.strip()))


def url_from_clipboard() -> str:
    cb = QGuiApplication.clipboard()
    clip = cb.text(QClipboard.Clipboard).strip()
    sel = cb.text(QClipboard.Selection).strip() if cb.supportsSelection() else ""
    for s in (clip, sel):
        if looks_like_url(s):
            return s
    return clip if "\n" not in clip else ""


def fetch_title(url: str) -> str:
    if url.startswith("www."):
        url = "https://" + url
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 (X11; Linux x86_64) zakladki"})
    with urllib.request.urlopen(req, timeout=6) as r:
        if "html" not in r.headers.get("Content-Type", "html"):
            return ""
        data = r.read(512 * 1024)
        charset = r.headers.get_content_charset()
        if r.headers.get("Content-Encoding") == "gzip":  # niektóre serwery pakują mimo braku Accept-Encoding
            data = zlib.decompressobj(16 + zlib.MAX_WBITS).decompress(data)
    if not charset:
        m = re.search(rb'<meta[^>]+charset=["\']?([\w-]+)', data, re.I)
        charset = m.group(1).decode() if m else "utf-8"
    text = data.decode(charset, errors="replace")
    m = re.search(r"<title[^>]*>(.*?)</title>", text, re.I | re.S)
    return " ".join(html.unescape(m.group(1)).split()) if m else ""


class TitleFetcher(QObject):
    done = Signal(str, str)  # url, tytuł

    def fetch(self, url):
        def run():
            try:
                title = fetch_title(url)
            except Exception:
                title = ""
            self.done.emit(url, title)
        threading.Thread(target=run, daemon=True).start()


class TagsEdit(QLineEdit):
    """Pole tagów rozdzielanych przecinkami z podpowiedziami dla ostatniego tagu."""

    def __init__(self, all_tags):
        super().__init__()
        self.comp = QCompleter(all_tags, self)
        self.comp.setCaseSensitivity(Qt.CaseInsensitive)
        self.comp.setFilterMode(Qt.MatchContains)
        self.comp.setWidget(self)
        self.comp.activated.connect(self.insert_tag)
        self.textEdited.connect(self.update_prefix)

    def current_word(self):
        return self.text()[:self.cursorPosition()].split(",")[-1].strip()

    def update_prefix(self):
        word = self.current_word()
        if not word:
            self.comp.popup().hide()
            return
        self.comp.setCompletionPrefix(word)
        if self.comp.completionCount():
            self.comp.complete()
        else:
            self.comp.popup().hide()

    def insert_tag(self, tag):
        before = self.text()[:self.cursorPosition()].rsplit(",", 1)
        head = before[0] + ", " if len(before) == 2 else ""
        self.setText(head + tag + ", ")

    def keyPressEvent(self, e):
        # gdy podpowiedzi są otwarte, Enter/Tab wybiera tag zamiast zapisywać
        if self.comp.popup().isVisible() and e.key() in (Qt.Key_Return, Qt.Key_Enter, Qt.Key_Tab):
            e.ignore()
            return
        super().keyPressEvent(e)


class BookmarkDialog(QDialog):
    def __init__(self, store: Store, url="", bid=None, parent=None):
        super().__init__(parent)
        self.store = store
        self.bid = bid
        self.resize(640, 0)

        self.url = QLineEdit(url)
        self.title = QLineEdit()
        self.tags = TagsEdit([t for t, _ in store.all_tags()])
        self.tags.setPlaceholderText("np. python, praca, do przeczytania")
        self.info = QLabel()
        self.info.setStyleSheet("color: gray")

        form = QFormLayout()
        form.addRow("Adres:", self.url)
        form.addRow("Tytuł:", self.title)
        form.addRow("Tagi:", self.tags)
        buttons = QDialogButtonBox(QDialogButtonBox.Save | QDialogButtonBox.Cancel)
        buttons.accepted.connect(self.accept)
        buttons.rejected.connect(self.reject)
        lay = QVBoxLayout(self)
        lay.addLayout(form)
        lay.addWidget(self.info)
        lay.addWidget(buttons)

        existing = store.get(bid) if bid else store.find_url(url) if url else None
        if existing:
            self.bid, url, title, tags = existing
            self.url.setText(url)
            self.title.setText(title)
            self.tags.setText(", ".join(tags) + (", " if tags else ""))
            if bid is None:
                self.info.setText("Ten adres już jest w zakładkach – możesz go edytować.")
        self.setWindowTitle("Edytuj zakładkę" if self.bid else "Dodaj zakładkę")

        self.fetcher = TitleFetcher(self)
        self.fetcher.done.connect(self.title_fetched)
        if not self.title.text() and looks_like_url(self.url.text()):
            self.title.setPlaceholderText("pobieram tytuł strony…")
            self.fetcher.fetch(self.url.text().strip())

        (self.tags if self.title.text() or not url else self.title).setFocus()

    def title_fetched(self, url, title):
        self.title.setPlaceholderText("")
        if url == self.url.text().strip() and title and not self.title.text():
            self.title.setText(title)
            self.title.selectAll()

    def accept(self):
        url = self.url.text().strip()
        if not url:
            self.info.setText("Podaj adres.")
            return
        other = self.store.find_url(url)
        if other and other[0] != self.bid:
            self.info.setText("Inna zakładka ma już ten adres.")
            return
        self.bid = self.store.save(url, self.title.text() or url, self.tags.text(), self.bid)
        super().accept()


# ------------------------------------------------------------------- wyszukiwarka

class ResultsModel(QAbstractTableModel):
    HEADERS = ["Tytuł", "Adres", "Tagi", "Dodano"]

    def __init__(self):
        super().__init__()
        self.raw = []   # kolejność z bazy: trafność albo najnowsze
        self.rows = []
        self.sort_col, self.sort_order = -1, Qt.AscendingOrder

    def set_rows(self, rows):
        self.beginResetModel()
        self.raw = rows
        self.rows = self._sorted()
        self.endResetModel()

    def sort(self, column, order=Qt.AscendingOrder):
        self.layoutAboutToBeChanged.emit()
        self.sort_col, self.sort_order = column, order
        self.rows = self._sorted()
        self.layoutChanged.emit()

    def _sorted(self):
        # kolumna -1 = bez sortowania (trzecie kliknięcie w nagłówek)
        if self.sort_col < 0:
            return list(self.raw)
        key = {0: lambda r: fold(r[1]), 1: lambda r: r[2].lower(),
               2: lambda r: fold(r[3] or ""), 3: lambda r: r[4]}[self.sort_col]
        return sorted(self.raw, key=key, reverse=self.sort_order == Qt.DescendingOrder)

    def rowCount(self, parent=QModelIndex()):
        return 0 if parent.isValid() else len(self.rows)

    def columnCount(self, parent=QModelIndex()):
        return len(self.HEADERS)

    def headerData(self, section, orientation, role=Qt.DisplayRole):
        if role == Qt.DisplayRole and orientation == Qt.Horizontal:
            return self.HEADERS[section]

    def data(self, index, role=Qt.DisplayRole):
        row = self.rows[index.row()]
        col = index.column()
        if role == Qt.DisplayRole:
            if col == 3:
                return time.strftime("%Y-%m-%d", time.localtime(row[4])) if row[4] else ""
            return row[col + 1] or ""
        if role == Qt.ToolTipRole and col in (0, 1):
            return f"{row[1]}\n{row[2]}"
        if role == Qt.ToolTipRole and col == 3 and row[4]:
            return time.strftime("%Y-%m-%d %H:%M", time.localtime(row[4]))

    def id_at(self, row):
        return self.rows[row][0]

    def url_at(self, row):
        return self.rows[row][2]


class MainWindow(QMainWindow):
    def __init__(self, store: Store):
        super().__init__()
        self.store = store
        self.setWindowTitle("Zakładki")
        self.resize(1200, 750)

        self.search = QLineEdit(placeholderText="Szukaj w tytułach, adresach i tagach…   "
                                                "(Enter – otwórz, Ctrl+N – dodaj, Esc – zamknij)")
        self.search.setClearButtonEnabled(True)
        self.search.textChanged.connect(lambda: self.timer.start())
        self.search.returnPressed.connect(self.open_first)
        self.search.installEventFilter(self)

        self.timer = QTimer(singleShot=True, interval=120)
        self.timer.timeout.connect(self.refresh)

        self.tag_list = QListWidget()
        self.tag_list.setSelectionMode(QAbstractItemView.MultiSelection)
        self.tag_list.itemSelectionChanged.connect(self.refresh)
        tag_label = QLabel("Tagi (kliknij, żeby filtrować)")
        tag_box = QWidget()
        tl = QVBoxLayout(tag_box)
        tl.setContentsMargins(0, 0, 0, 0)
        tl.addWidget(tag_label)
        tl.addWidget(self.tag_list)

        self.model = ResultsModel()
        self.table = QTableView()
        self.table.setModel(self.model)
        self.table.setSelectionBehavior(QAbstractItemView.SelectRows)
        self.table.setEditTriggers(QAbstractItemView.NoEditTriggers)
        self.table.verticalHeader().hide()
        self.table.setWordWrap(False)
        self.table.setAlternatingRowColors(True)
        header = self.table.horizontalHeader()
        # tytuł i adres dzielą wolne miejsce, tagi i data mają stałą szerokość
        header.setSectionResizeMode(0, QHeaderView.Stretch)
        header.setSectionResizeMode(1, QHeaderView.Stretch)
        header.setSectionResizeMode(2, QHeaderView.Interactive)
        header.setSectionResizeMode(3, QHeaderView.ResizeToContents)
        header.setMinimumSectionSize(60)
        header.setStretchLastSection(False)
        self.table.setColumnWidth(2, 160)
        self.table.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
        self.table.installEventFilter(self)
        # klik w nagłówek sortuje; trzeci klik wraca do kolejności trafności / najnowszych
        header.setSortIndicatorClearable(True)
        header.setSortIndicator(-1, Qt.AscendingOrder)
        self.table.setSortingEnabled(True)
        self.table.doubleClicked.connect(lambda idx: self.open_rows([idx.row()]))
        self.table.setContextMenuPolicy(Qt.CustomContextMenu)
        self.table.customContextMenuRequested.connect(self.context_menu)

        self.splitter = splitter = QSplitter()
        splitter.addWidget(tag_box)
        splitter.addWidget(self.table)
        splitter.setStretchFactor(0, 0)
        splitter.setStretchFactor(1, 1)
        splitter.setSizes([200, 1000])
        tag_label.setWordWrap(True)
        tag_box.setMinimumWidth(90)

        central = QWidget()
        lay = QVBoxLayout(central)
        lay.addWidget(self.search)
        lay.addWidget(splitter)
        self.setCentralWidget(central)

        # zmiany z innych komputerów (Syncthing) – odświeżamy widok
        self.sync_timer = QTimer(singleShot=True, interval=700)
        self.sync_timer.timeout.connect(self.sync_from_disk)
        self.watcher = QFileSystemWatcher([str(store.path.parent)], self)
        self.watcher.directoryChanged.connect(lambda: self.sync_timer.start())

        self.build_menu()
        self.reload_tags()
        self.refresh()
        self.search.setFocus()

    def sync_from_disk(self):
        if self.store.sync_from_disk():
            self.reload()
            self.statusBar().showMessage("Wczytano zmiany z synchronizacji", 5000)

    # -- menu / skróty
    def build_menu(self):
        z = self.menuBar().addMenu("&Zakładki")
        z.addAction("&Dodaj…", QKeySequence.New, self.add_bookmark)
        z.addAction("&Edytuj…", QKeySequence("F2"), self.edit_selected)
        z.addAction("&Otwórz", QKeySequence("Ctrl+Return"), self.open_selected)
        z.addAction("&Kopiuj adres", QKeySequence.Copy, self.copy_selected)
        z.addAction("&Usuń", QKeySequence.Delete, self.delete_selected)
        z.addSeparator()
        z.addAction("Import z &Firefoksa", self.import_firefox)
        z.addAction("Import z pliku &HTML…", self.import_html)
        z.addSeparator()
        z.addAction("&Zamknij", QKeySequence.Quit, self.close)

        focus = QAction(self, shortcut=QKeySequence.Find,
                        triggered=lambda: (self.search.setFocus(), self.search.selectAll()))
        esc = QAction(self, shortcut=QKeySequence("Esc"), triggered=self.escape)
        self.addActions([focus, esc])

    def eventFilter(self, obj, e):
        # wąskie okno: najpierw chowamy adres (jest w dymku), potem tagi
        if obj is self.table and e.type() == e.Type.Resize:
            w = e.size().width()
            self.table.setColumnHidden(1, w < 650)
            self.table.setColumnHidden(2, w < 420)
            self.table.setColumnHidden(3, w < 260)
            return False
        # strzałki w polu wyszukiwania przewijają wyniki
        if obj is self.search and e.type() == e.Type.KeyPress and e.key() in (Qt.Key_Down, Qt.Key_Up):
            rows = self.model.rowCount()
            if rows:
                cur = self.table.currentIndex().row()
                cur = min(cur + 1, rows - 1) if e.key() == Qt.Key_Down else max(cur - 1, 0)
                self.table.selectRow(cur)
            return True
        return super().eventFilter(obj, e)

    def resizeEvent(self, e):
        # panel tagów ~1/5 okna, w granicach 90–220 px
        super().resizeEvent(e)
        total = sum(self.splitter.sizes())
        tags = max(90, min(220, total // 5))
        self.splitter.setSizes([tags, total - tags])

    def escape(self):
        if self.search.text():
            self.search.clear()
        elif self.tag_list.selectedItems():
            self.tag_list.clearSelection()
        else:
            self.close()

    # -- dane
    def selected_tags(self):
        return [i.data(Qt.UserRole) for i in self.tag_list.selectedItems()]

    def refresh(self):
        rows = self.store.search(self.search.text(), self.selected_tags())
        self.model.set_rows(rows)
        if rows:
            self.table.selectRow(0)
        more = " (pokazano pierwsze)" if len(rows) == RESULT_LIMIT else ""
        self.statusBar().showMessage(
            f"Wyniki: {len(rows)}{more}   •   wszystkich zakładek: {self.store.count()}")

    def reload_tags(self):
        selected = set(self.selected_tags())
        self.tag_list.blockSignals(True)
        self.tag_list.clear()
        for tag, n in self.store.all_tags():
            item = QListWidgetItem(f"{tag}  ({n})")
            item.setData(Qt.UserRole, tag)
            self.tag_list.addItem(item)
            item.setSelected(tag in selected)
        self.tag_list.blockSignals(False)

    def reload(self):
        self.reload_tags()
        self.refresh()

    # -- importy
    def import_firefox(self):
        profiles = find_firefox_profiles()
        if not profiles:
            f, _ = QFileDialog.getOpenFileName(self, "Wskaż places.sqlite", str(Path.home()),
                                               "places.sqlite (places.sqlite)")
            profiles = [Path(f)] if f else []
        if len(profiles) > 1:
            choice, ok = QInputDialog.getItem(self, "Firefox", "Wybierz profil:",
                                              [str(p) for p in profiles], 0, False)
            profiles = [Path(choice)] if ok else []
        if profiles:
            self.run_import(read_firefox, profiles[0])

    def import_html(self):
        f, _ = QFileDialog.getOpenFileName(self, "Plik zakładek HTML", str(Path.home()),
                                           "HTML (*.html *.htm);;Wszystkie pliki (*)")
        if f:
            self.run_import(read_html, Path(f))

    def run_import(self, reader, path):
        QApplication.setOverrideCursor(Qt.WaitCursor)
        try:
            n = self.store.import_items(reader(path))
        except Exception as exc:
            QApplication.restoreOverrideCursor()
            QMessageBox.critical(self, "Błąd importu", f"{path}\n\n{exc}")
            return
        QApplication.restoreOverrideCursor()
        self.reload()
        self.statusBar().showMessage(f"Dodano {n} nowych zakładek z: {path}", 8000)

    # -- akcje na wynikach
    def selected_rows(self):
        return sorted({i.row() for i in self.table.selectionModel().selectedRows()})

    def open_rows(self, rows):
        for r in rows[:20]:
            QDesktopServices.openUrl(QUrl.fromUserInput(self.model.url_at(r)))

    def open_selected(self):
        self.open_rows(self.selected_rows())

    def open_first(self):
        self.open_rows(self.selected_rows() or ([0] if self.model.rowCount() else []))

    def copy_selected(self):
        if self.search.hasFocus() and self.search.hasSelectedText():
            self.search.copy()
            return
        rows = self.selected_rows()
        if rows:
            QGuiApplication.clipboard().setText("\n".join(self.model.url_at(r) for r in rows))
            self.statusBar().showMessage("Skopiowano adres", 3000)

    def add_bookmark(self):
        if BookmarkDialog(self.store, url_from_clipboard(), parent=self).exec():
            self.reload()

    def edit_selected(self):
        rows = self.selected_rows()
        if rows and BookmarkDialog(self.store, bid=self.model.id_at(rows[0]), parent=self).exec():
            self.reload()

    def delete_selected(self):
        rows = self.selected_rows()
        if not rows or (self.search.hasFocus() and self.search.text()):
            return
        titles = "\n".join(self.model.rows[r][1] for r in rows[:10])
        if QMessageBox.question(self, "Usuń", f"Usunąć {len(rows)} zakładek?\n\n{titles}") == QMessageBox.Yes:
            self.store.delete([self.model.id_at(r) for r in rows])
            self.reload()

    def context_menu(self, pos):
        if not self.selected_rows():
            return
        m = QMenu(self)
        m.addAction("Otwórz", self.open_selected)
        m.addAction("Edytuj…", self.edit_selected)
        m.addAction("Kopiuj adres", self.copy_selected)
        m.addSeparator()
        m.addAction("Usuń", self.delete_selected)
        m.exec(self.table.viewport().mapToGlobal(pos))


# ------------------------------------------------------------------------ start

def notify(title, body):
    if shutil.which("notify-send"):
        subprocess.Popen(["notify-send", title, body])


def main():
    ap = argparse.ArgumentParser(description="Zakładki z tagami")
    ap.add_argument("--add", nargs="?", const="", metavar="URL",
                    help="dodaj zakładkę (bez URL – adres ze schowka)")
    args = ap.parse_args()

    app = QApplication(sys.argv[:1])
    app.setApplicationName("zakladki")
    app.setDesktopFileName("zakladki")
    store = Store(db_path())

    if args.add is not None:
        dlg = BookmarkDialog(store, args.add or url_from_clipboard())
        if dlg.exec():
            notify("Zakładka zapisana", dlg.url.text())
        return

    win = MainWindow(store)
    win.show()
    if store.count() == 0 and find_firefox_profiles():
        if QMessageBox.question(win, "Pierwsze uruchomienie",
                                "Baza jest pusta. Zaimportować zakładki z Firefoksa?") == QMessageBox.Yes:
            win.import_firefox()
    sys.exit(app.exec())


if __name__ == "__main__":
    main()
