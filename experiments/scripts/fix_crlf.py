#!/usr/bin/env python3
"""Rewrite a file to use Unix (LF) line endings. Usage: python fix_crlf.py <path>"""
import sys
from pathlib import Path

if len(sys.argv) != 2:
    sys.exit("Usage: python fix_crlf.py <file path>")
path = Path(sys.argv[1])
if not path.exists():
    sys.exit("File not found: %s" % path)
raw = path.read_bytes()
out = raw.replace(b"\r\n", b"\n").replace(b"\r", b"\n")
if out != raw:
    path.write_bytes(out)
    print("Fixed: %s" % path)
else:
    print("Already LF: %s" % path)
