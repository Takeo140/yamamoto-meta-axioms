# License Apache 2.0
# Author: Takeo Yamamoto

from dataclasses import dataclass
from typing import Callable, TypeVar, Generic, Dict, Iterable

X = TypeVar("X")   # 生成テキスト・コンテキスト空間
I = TypeVar("I")   # モデルインデックス空間


# ─────────────────────────────────────────────────
# 不確実性・コスト判定構造 (Uncertainty Evaluator)
# ─────────────────────────────────────────────────
@dataclass
class UncertaintyEvaluator(Generic[X]):
    # 不確実性を評価する関数 u(x)
    uncertainty: Callable[[X], float]
    # 閾値
    threshold: float

    def __post_init__(self):
        assert self.threshold > 0, "threshold must be positive"


# ─────────────────────────────────────────────────
# 動的スパース重み分配 (Adaptive Sparse Weights)
# ─────────────────────────────────────────────────
@dataclass
class AdaptiveEnsemble(Generic[X, I]):
    # 不確実性評価器
    eval: UncertaintyEvaluator[X]
    # 重み関数 w(x)[i]
    w: Callable[[X], Dict[I, float]]
    # サンプルコスト c(i, x)
    sampleCost: Callable[[I, X], float]
    # スパース化に用いる「代表モデル」
    arbitrary_index: I

    def hNonNeg(self, x: X, i: I) -> bool:
        return self.w(x)[i] >= 0.0

    def hSum(self, x: X) -> float:
        return sum(self.w(x).values())

    def hSparse(self, x: X) -> bool:
        """
        Lean版の hSparse:
        eval.uncertainty x < eval.threshold → すべての重みが
        arbitrary_index に 1、それ以外 0 になることを表現。
        Pythonでは「そうなるように w を設計する」前提で、
       チェック関数として実装。
        """
        if self.eval.uncertainty(x) < self.eval.threshold:
            w_x = self.w(x)
            for i, wi in w_x.items():
                if i == self.arbitrary_index:
                    if wi != 1.0:
                        return False
                else:
                    if wi != 0.0:
                        return False
        return True


# ─────────────────────────────────────────────────
# 動的アンサンブルにおけるハルシネーション期待値コスト
# ─────────────────────────────────────────────────
def adaptiveExpectedCost(E: AdaptiveEnsemble[X, I], x: X) -> float:
    w_x = E.w(x)
    return sum(w_x[i] * E.sampleCost(i, x) for i in w_x.keys())


# Lemma: 期待値コストの非負有界性（Python版ではチェック関数）
def adaptive_cost_nonneg(
    E: AdaptiveEnsemble[X, I],
    hC: Callable[[I, X], float],  # ここでは「コストが非負であること」を返す関数とみなす
    x: X,
) -> bool:
    """
    Lean版の定理:
      0 ≤ adaptiveExpectedCost E x
    を、Pythonでは「非負かどうかをチェックする」関数として表現。
    """
    cost = adaptiveExpectedCost(E, x)
    return cost >= 0.0


# Theorem: 低不確実性下におけるコスト計算の縮約（Python版）
def adaptive_cost_sparse_reduction(E: AdaptiveEnsemble[X, I], x: X) -> float:
    """
    Lean版の定理:
      eval.uncertainty x < eval.threshold のとき
      adaptiveExpectedCost E x = sampleCost(arbitrary_index, x)

    Pythonでは、その状況を前提に「縮約されたコスト」を返す。
    """
    assert E.eval.uncertainty(x) < E.eval.threshold, "Low uncertainty condition must hold"
    # スパース性が満たされていることを確認（設計上そうなっている前提）
    assert E.hSparse(x), "Weights must be sparse under low uncertainty"
    return E.sampleCost(E.arbitrary_index, x)


# ─────────────────────────────────────────────────
# [NEW] ハルシネーション（誤謬）確率モデル
# ─────────────────────────────────────────────────
@dataclass
class ErrorModel(Generic[X, I]):
    # 各モデルの誤差率 e(i, x)
    errorRate: Callable[[I, X], float]

    def hNonNeg(self, i: I, x: X) -> bool:
        return self.errorRate(i, x) >= 0.0


# ─────────────────────────────────────────────────
# [NEW] アンサンブル適用時の期待ハルシネーション誤差
# ─────────────────────────────────────────────────
def expectedError(E: AdaptiveEnsemble[X, I], Err: ErrorModel[X, I], x: X) -> float:
    w_x = E.w(x)
    return sum(w_x[i] * Err.errorRate(i, x) for i in w_x.keys())


# ─────────────────────────────────────────────────
# [NEW] Theorem: リスク上限の数学的保証 (Error Upper Bound)
# ─────────────────────────────────────────────────
def ensemble_error_upper_bound(
    E: AdaptiveEnsemble[X, I],
    Err: ErrorModel[X, I],
    x: X,
    M: float,
    indices: Iterable[I],
) -> float:
    """
    Lean版の定理:
      すべての i について errorRate(i, x) ≤ M なら、
      expectedError(E, Err, x) ≤ M

    Pythonでは、期待誤差を計算し、その値を返す。
    利用側で「<= M かどうか」をチェックできる。
    """
    w_x = E.w(x)

    # 上界付きの誤差を計算
    upper_sum = 0.0
    for i in indices:
        wi = w_x.get(i, 0.0)
        # errorRate(i, x) ≤ M を仮定
        upper_sum += wi * M

    # ∑ w_i = 1 を仮定（設計上そうなるように w を定義）
    assert abs(E.hSum(x) - 1.0) < 1e-8, "Weights must sum to 1"

    # upper_sum は M に等しいはず
    # expectedError(E, Err, x) ≤ upper_sum ≤ M という構造を模倣
    err = expectedError(E, Err, x)
    return err  # 利用側で err <= M を確認する
