"""Numpy detectors for the CipherGuard gate (Stage 04).

Two framings, because the held-out-T6 question divides them:
  * LogisticDetector -- supervised tampered-vs-clean. Strong in-distribution; may
    struggle on a tamper TYPE never seen in training (the honest E2 tension).
  * OneClassDetector -- fits ONLY clean structure and flags deviations. This is the
    principled framing for detecting an unseen tamper mechanism (novel T6).

Both are deliberately simple (few params) to avoid overfitting 222 items; the full
GAT+MLP is the cluster model (Phase 5).
"""
from __future__ import annotations
import numpy as np


class Standardizer:
    def fit(self, X: np.ndarray) -> "Standardizer":
        self.mean_ = X.mean(axis=0)
        self.std_ = X.std(axis=0) + 1e-8
        return self

    def transform(self, X: np.ndarray) -> np.ndarray:
        return (X - self.mean_) / self.std_


class LogisticDetector:
    """L2-regularized logistic regression, full-batch gradient descent."""
    def __init__(self, l2: float = 1e-2, lr: float = 0.1, epochs: int = 800, seed: int = 0):
        self.l2, self.lr, self.epochs, self.seed = l2, lr, epochs, seed

    def fit(self, X: np.ndarray, y: np.ndarray) -> "LogisticDetector":
        rng = np.random.default_rng(self.seed)
        n, d = X.shape
        self.w = rng.normal(0, 0.01, d)
        self.b = 0.0
        # inverse-frequency class weights (avoid degenerate all-positive on imbalance)
        n_pos, n_neg = max(1, int(y.sum())), max(1, int((1 - y).sum()))
        sw = np.where(y == 1, n / (2.0 * n_pos), n / (2.0 * n_neg))
        for _ in range(self.epochs):
            z = np.clip(X @ self.w + self.b, -30, 30)
            p = 1.0 / (1.0 + np.exp(-z))
            g = (p - y) * sw
            gw = X.T @ g / n + self.l2 * self.w
            gb = g.mean()
            self.w -= self.lr * gw
            self.b -= self.lr * gb
        return self

    def score(self, X: np.ndarray) -> np.ndarray:
        return 1.0 / (1.0 + np.exp(-np.clip(X @ self.w + self.b, -30, 30)))


class OneClassDetector:
    """Diagonal-Gaussian one-class model: fit clean, score = normalized sq. deviation.
    Higher score = more anomalous. Threshold set from the clean training scores."""
    def __init__(self, quantile: float = 0.99):
        self.quantile = quantile

    def fit(self, X_clean: np.ndarray) -> "OneClassDetector":
        self.mean_ = X_clean.mean(axis=0)
        self.var_ = X_clean.var(axis=0) + 1e-6
        s = self._raw(X_clean)
        self.threshold_ = float(np.quantile(s, self.quantile)) if len(s) > 1 else float(s.max())
        return self

    def _raw(self, X: np.ndarray) -> np.ndarray:
        return np.sum((X - self.mean_) ** 2 / self.var_, axis=1)

    def score(self, X: np.ndarray) -> np.ndarray:
        """Return a [0,1]-ish anomaly score via threshold-relative logistic squash."""
        raw = self._raw(X)
        return 1.0 / (1.0 + np.exp(-(raw - self.threshold_) / (abs(self.threshold_) + 1e-6)))

    def predict(self, X: np.ndarray) -> np.ndarray:
        return (self._raw(X) > self.threshold_).astype(int)
