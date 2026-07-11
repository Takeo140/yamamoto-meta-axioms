License Apache 2.0  Takeo Yamamoto
/-
  Meta-axiomatic computation theory in Lean
  （極値原理・トポロジー・整合性・多層抽象・オブバース／リバース）
-/

universe u v

/-- 抽象的な状態空間（位相構造はここでは抽象化して型として扱う） -/
structure StateSpace (α : Type u) :=
  (carrier : Type u := α)

/-- 抽象的な出力空間 -/
structure OutputSpace (β : Type v) :=
  (carrier : Type v := β)

/-- 計算（プログラム）：状態から出力への写像 -/
structure Program (α : Type u) (β : Type v) :=
  (run : α → β)

/-- コスト密度 L：状態と出力に対する「計算コスト」 -/
def CostDensity (α : Type u) (β : Type v) :=
  α → β → ℝ

/-- 離散版の「作用」：入力列に対する総コスト -/
def action {α β : Type u} (L : CostDensity α β) (p : Program α β) (xs : List α) : ℝ :=
  xs.foldl (fun acc x => acc + L x (p.run x)) 0

/-- 仕様：入力と出力の関係が正しいかどうかを判定する述語 -/
def Spec (α : Type u) (β : Type v) :=
  α → β → Prop

/-- プログラムが仕様と整合している（論理的一貫性） -/
def consistent {α β : Type u} (φ : Spec α β) (p : Program α β) : Prop :=
  ∀ x : α, φ x (p.run x)

/-- 多層抽象：状態空間をレイヤー分解したもの -/
structure LayeredState (ι : Type u) (α : ι → Type u) :=
  (state : ∀ i : ι, α i)

/-- レイヤーごとの部分プログラム -/
structure LayerProgram (ι : Type u) (α : ι → Type u) (β : ι → Type v) :=
  (runLayer : ∀ i : ι, α i → β i)

/-- 全体プログラムへの束ね -/
def LayerProgram.toProgram {ι : Type u} {α : ι → Type u} {β : ι → Type v}
  (P : LayerProgram ι α β) :
  LayeredState ι α → LayeredState ι β :=
  fun s => { state := fun i => P.runLayer i (s.state i) }

/-- オブバース（物理）とリバース（数学）の対応写像 -/
structure DualState (α_phys α_math : Type u) :=
  (toMath : α_phys → α_math)

/-- 物理プログラムと数学プログラムの「双対的一致条件」 -/
def dualConsistent
  {α_phys α_math β_phys β_math : Type u}
  (Φ : DualState α_phys α_math)
  (Ψ : DualState β_phys β_math)
  (p_phys : Program α_phys β_phys)
  (p_math : Program α_math β_math) : Prop :=
  ∀ x : α_phys, Ψ.toMath (p_phys.run x) = p_math.run (Φ.toMath x)

/-- 極値原理：与えられた候補集合上で作用を極小化するプログラム -/
def optimalProgram
  {α β : Type u}
  (L : CostDensity α β)
  (xs : List α)
  (candidates : List (Program α β)) : Option (Program α β) :=
  candidates.foldl
    (fun best p =>
      match best with
      | none      => some p
      | some p₀   =>
        if action L p xs < action L p₀ xs then some p else best)
    none
