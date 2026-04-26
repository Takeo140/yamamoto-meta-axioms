import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.DeriveToExpr
import Mathlib.Tactic.Linarith

namespace CancerRepair

/-- 塩基の定義を強化 -/
inductive Base : Type
  | A | T | G | C
  deriving Repr, DecidableEq, Inhabited

/-- 塩基の物理化学的エンコード（正規化） -/
def Base.weight : Base → Nat
  | .A => 5 | .G => 6 | .C => 3 | .T => 0

/-- アミノ酸の機能クラス（より詳細な分類へ） -/
inductive FuncClass : Type
  | aromatic | hydrophobic | flexible | polar | positive | negative | stop
  deriving Repr, DecidableEq

/-- 
  コドンを構造体（Structure）として定義。
  これにより、各ポジションへのアクセスと意味付けを厳格化する。
-/
structure Codon where
  p1 : Base
  p2 : Base
  p3 : Base
  deriving Repr, DecidableEq, Inhabited

/-- 翻訳ロジックの整理（パターンマッチの最適化） -/
def Codon.funcClass : Codon → FuncClass
  | ⟨.G, .G, _⟩ => .flexible
  | ⟨.G, .T, _⟩ | ⟨.C, .T, _⟩ | ⟨.T, .T, .A⟩ | ⟨.T, .T, .G⟩ | ⟨.A, .T, _⟩ | ⟨.G, .C, _⟩ | ⟨.C, .C, _⟩ => .hydrophobic
  | ⟨.T, .T, .T⟩ | ⟨.T, .T, .C⟩ | ⟨.T, .G, .G⟩ | ⟨.T, .A, .T⟩ | ⟨.T, .A, .C⟩ => .aromatic
  | ⟨.A, .A, .A⟩ | ⟨.A, .A, .G⟩ | ⟨.C, .G, _⟩ | ⟨.A, .G, .A⟩ | ⟨.A, .G, .G⟩ => .positive
  | ⟨.G, .A, .T⟩ | ⟨.G, .A, .C⟩ | ⟨.G, .A, .A⟩ | ⟨.G, .A, .G⟩ => .negative
  | ⟨.T, .A, .A⟩ | ⟨.T, .A, .G⟩ | ⟨.T, .G, .A⟩ => .stop
  | _ => .polar

/-- 
  機能距離（FD）スコアの再定義
  if-then-else を直接数値計算に組み込む形式にし、証明を容易にする。
-/
def fd_score (wt mut : Codon) : Nat :=
  let h5 := if wt.funcClass = mut.funcClass then 0 else 4
  let h1 := if wt.p1.weight = mut.p1.weight then 0 else 3
  let h2 := if wt.p2.weight = mut.p2.weight then 0 else 2
  let h3 := if wt.p3.weight = mut.p3.weight then 0 else 1
  h5 + h1 + h2 + h3

/-- 
  癌治療の「修復安全性」を保証する述語 
  単なる修復ではなく、修復後のスコアが野生型に限りなく近いことを要求する。
-/
def is_safe_repair (wt mut repair : Codon) : Prop :=
  fd_score wt repair < fd_score wt mut ∧ (repair.funcClass = wt.funcClass)

/-- 主定理の強化：すべての主要ドライバー変異に対して、安全な修復が存在する -/
theorem exist_safe_repair (wt mut : Codon) (h : fd_score wt mut ≥ 6) :
    ∃ r, is_safe_repair wt mut r := by
  refine ⟨wt, ?_⟩
  constructor
  · have : fd_score wt wt = 0 := by simp [fd_score]
    rw [this]
    linarith
  · rfl

/-- 
  治療シミュレーション用の実例データ 
  KRAS G12D (GGT -> GAT)
-/
def kras_wt  : Codon := ⟨.G, .G, .T⟩
def kras_mut : Codon := ⟨.G, .A, .T⟩

example : fd_score kras_wt kras_mut = 6 := by native_decide

end CancerRepair
