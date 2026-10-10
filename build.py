#!/usr/bin/env python3
"""Build index.html (one self-contained file) from the sources in src/."""
from pathlib import Path

src = Path(__file__).parent / "src"
page = (src / "page.html").read_text(encoding="utf-8")
cut = page.index('<div class="app"')
head, body = page[:cut], page[cut:]

boot = (
    "<script>\n"
    "window.onerror=function(m,s,l,c){var e=document.getElementById('booterr');"
    "if(e)e.textContent='Error: '+m+' (line '+l+':'+c+')';"
    "var t=document.querySelector('#boot .hint');"
    "if(t&&e)t.textContent='הקוד נתקל בשגיאה בדפדפן הזה. שלח לי את השורה הבאה:'};\n"
    "</script>\n"
)
app = (
    "<script>\nconst DATA=" + (src / "data.json").read_text(encoding="utf-8") + ";\n"
    + (src / "core.js").read_text(encoding="utf-8") + "\n"
    + (src / "sheet.js").read_text(encoding="utf-8") + "\n"
    + (src / "logic.js").read_text(encoding="utf-8") + "\n"
    + (src / "gf.js").read_text(encoding="utf-8") + "\n"
    + (src / "rel.js").read_text(encoding="utf-8") + "\n"
    + (src / "ui.js").read_text(encoding="utf-8") + "\n</script>\n"
)
html = (
    '<!doctype html>\n<html lang="he" dir="rtl">\n<head>\n<meta charset="utf-8">\n'
    '<meta name="viewport" content="width=device-width, initial-scale=1">\n'
    + head + "</head>\n<body>\n" + body + boot + app + "</body>\n</html>\n"
)
(Path(__file__).parent / "index.html").write_text(html, encoding="utf-8")
print("index.html", len(html), "bytes")
