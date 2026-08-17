"""Cluster-tail-friendly checkpoint logging for CipherGuard.

Every stage uses one StageLogger so the user can follow a batch job by tailing a
log and pinpoint exactly where a failure happened (CLAUDE.md Section 6). Output
goes to BOTH the console and logs/<stage>/<timestamp>.log.

Format:  [CipherGuard][<stage>] [CKPT k/N] <message>
"""
from __future__ import annotations
import sys
import time
from datetime import datetime

from .paths import LOGS, ensure


class StageLogger:
    def __init__(self, stage: str):
        self.stage = stage
        self.t0 = time.time()
        log_dir = ensure(LOGS / stage)
        ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        self.log_path = log_dir / f"{ts}.log"
        self._fh = open(self.log_path, "w")
        self.info(f"logging to {self.log_path}")

    def _emit(self, line: str) -> None:
        print(line, flush=True)
        self._fh.write(line + "\n")
        self._fh.flush()

    def _fmt(self, msg: str, ckpt: str | None) -> str:
        tag = f"[CKPT {ckpt}] " if ckpt else ""
        return f"[CipherGuard][{self.stage}] {tag}{msg}"

    def info(self, msg: str, ckpt: str | None = None) -> None:
        self._emit(self._fmt(msg, ckpt))

    def ckpt(self, msg: str, k: int, n: int) -> None:
        self.info(msg, ckpt=f"{k}/{n}")

    def warn(self, msg: str) -> None:
        self.info(f"WARNING: {msg}")

    def error(self, msg: str) -> None:
        self.info(f"ERROR: {msg}")

    def fail(self, msg: str) -> "RuntimeError":
        """Log loudly and return an exception to raise (fail-loud discipline)."""
        self.error(msg)
        return RuntimeError(f"[{self.stage}] {msg}")

    def done(self, msg: str = "") -> None:
        self.info(f"DONE {msg} (wall-clock {time.time() - self.t0:.1f}s)")

    def close(self) -> None:
        self._fh.close()


def get_logger(stage: str) -> StageLogger:
    return StageLogger(stage)
