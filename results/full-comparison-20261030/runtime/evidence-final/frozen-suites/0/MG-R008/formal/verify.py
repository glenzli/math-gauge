#!/usr/bin/env python3
"""Portable case entry point; all verification is owned by scripts/formal."""
from pathlib import Path
import subprocess,sys
root=Path(__file__).resolve()
raise SystemExit(subprocess.call([sys.executable,str(root.parents[4]/'scripts/formal/verify.py'),'--manifest',str(root.parent/'manifest.json'),*sys.argv[1:]]))
