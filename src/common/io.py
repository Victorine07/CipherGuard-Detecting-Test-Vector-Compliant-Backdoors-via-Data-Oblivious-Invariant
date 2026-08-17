"""Small JSON IO helpers that always create parent dirs (fail-loud on read)."""
from __future__ import annotations
import json
from pathlib import Path
from typing import Any


def write_json(path: Path, obj: Any, indent: int = 2) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=indent, default=str))
    return path


def read_json(path: Path) -> Any:
    if not path.exists():
        raise FileNotFoundError(f"expected JSON not found: {path}")
    return json.loads(path.read_text())


def write_text(path: Path, text: str) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)
    return path
