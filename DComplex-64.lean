License Apache 2.0  Takeo Yamamoto
import Mathlib

/-
============================================================
UHA-DComplex-64 (離散計算核)
============================================================
-/

abbrev U64 := ZMod (2^64)

structure DComplex where
  re : U64
  im : U64
deriving DecidableEq, Repr

instance : Zero DComplex := ⟨0,0⟩

instance : Add DComplex :=
  ⟨fun a b => ⟨a.re + b.re, a.im + b.im⟩⟩

instance : Sub DComplex :=
  ⟨fun a b => ⟨a.re - b.re, a.im - b.im⟩⟩

instance : Mul DComplex :=
  ⟨fun a b =>
    ⟨a.re * b.re - a.im * b.im,
     a.re * b.im + a.im * b.re⟩⟩

abbrev WorldState (n : Nat) := Fin n → DComplex

def delta {n} (a b : WorldState n) : WorldState n :=
  fun i => a i - b i

/-
============================================================
連続物理層 (ApexDiscovery)
============================================================
-/

abbrev Scalar := ℚ

structure State where
  q : Scalar
  p : Scalar
deriving DecidableEq, Repr

structure Sample where
  t : Nat
  state : State
deriving DecidableEq, Repr

abbrev Trajectory := List Sample

def velocity (dt : Scalar) (a b : State) : Scalar :=
  (b.q - a.q) / dt

def acceleration (dt : Scalar) (a b c : State) : Scalar :=
  (c.q - 2*b.q + a.q) / (dt*dt)

/-
============================================================
力学法則 AST
============================================================
-/

inductive LawExpr where
  | constant : Scalar → LawExpr
  | q : LawExpr
  | p : LawExpr
  | v : LawExpr
  | add : LawExpr → LawExpr → LawExpr
  | sub : LawExpr → LawExpr → LawExpr
  | mul : LawExpr → LawExpr → LawExpr
  | neg : LawExpr → LawExpr
  | square : LawExpr → LawExpr
deriving DecidableEq, Repr

namespace LawExpr

def eval (q p v : Scalar) : LawExpr → Scalar
  | constant c => c
  | q => q
  | p => p
  | v => v
  | add a b => eval q p v a + eval q p v b
  | sub a b => eval q p v a - eval q p v b
  | mul a b => eval q p v a * eval q p v b
  | neg a => - eval q p v a
  | square a => (eval q p v a)^2

def size : LawExpr → Nat
  | constant _ => 1
  | q => 1
  | p => 1
  | v => 1
  | add a b => 1 + size a + size b
  | sub a b => 1 + size a + size b
  | mul a b => 1 + size a + size b
  | neg a => 1 + size a
  | square a => 1 + size a

end LawExpr

/-
============================================================
Regression Data
============================================================
-/

structure RegressionPoint where
  q : Scalar
  p : Scalar
  v : Scalar
  acceleration : Scalar
deriving DecidableEq, Repr

abbrev RegressionData := List RegressionPoint

def makePoint (dt : Scalar) (a b c : State) : RegressionPoint :=
  {
    q := b.q,
    p := b.p,
    v := velocity dt a b,
    acceleration := acceleration dt a b c
  }

def makeRegressionData (dt : Scalar) : Trajectory → RegressionData
  | a :: b :: c :: rest =>
      makePoint dt a.state b.state c.state ::
      makeRegressionData dt (b :: c :: rest)
  | _ => []

/-
============================================================
Residual / Falsification
============================================================
-/

def forceResidual (law : LawExpr) (pt : RegressionPoint) (mass : Scalar) : Scalar :=
  mass * pt.acceleration - law.eval pt.q pt.p pt.v

def totalResidual (law : LawExpr) (data : RegressionData) (mass : Scalar) : Scalar :=
  data.foldl (fun acc pt => acc + |forceResidual law pt mass|) 0

def exactLaw (law : LawExpr) (data : RegressionData) (mass : Scalar) : Prop :=
  ∀ pt ∈ data, forceResidual law pt mass = 0

/-
============================================================
候補生成
============================================================
-/

def atoms : List LawExpr :=
  [.constant (-1), .constant 0, .constant 1, .q, .p, .v]

def generate : Nat → List LawExpr
  | 0 => atoms
  | n+1 =>
      let prev := generate n
      prev ++
      prev.map LawExpr.neg ++
      prev.map LawExpr.square ++
      (prev.bind fun a =>
        prev.map fun b => LawExpr.add a b) ++
      (prev.bind fun a =>
        prev.map fun b => LawExpr.sub a b) ++
      (prev.bind fun a =>
        prev.map fun b => LawExpr.mul a b)

/-
============================================================
モデル選択
============================================================
-/

def modelScore (law : LawExpr) (data : RegressionData)
    (mass λ : Scalar) : Scalar :=
  totalResidual law data mass + λ * (law.size)

def better (a b : LawExpr) (data : RegressionData)
    (mass λ : Scalar) : LawExpr :=
  if modelScore a data mass λ < modelScore b data mass λ
  then a else b

def selectBest (cands : List LawExpr)
    (data : RegressionData) (mass λ : Scalar) :
    Option LawExpr :=
  cands.foldl
    (fun best cand =>
      match best with
      | none => some cand
      | some cur => some (better cand cur data mass λ))
    none

/-
============================================================
離散 ↔ 連続 写像（物理的に正しい形）
============================================================
-/

def scale : Scalar := 1 / (2^32)

def liftState {n} (ws : WorldState n) : State :=
  let dc := ws 0
  {
    q := scale * dc.re.val,
    p := scale * dc.im.val
  }

def lowerState {n} (s : State) : WorldState n :=
  fun _ =>
    let re := U64.ofNat (s.q / scale).num
    let im := U64.ofNat (s.p / scale).num
    ⟨re, im⟩

/-
============================================================
LawExpr → 離散 PhysicsLaw 変換
============================================================
-/

structure PhysicsLaw (n : Nat) where
  evolve : WorldState n → WorldState n
  name : String

def lawToPhysics {n}
    (dt mass : Scalar)
    (law : LawExpr) :
    PhysicsLaw n :=
{
  evolve := fun ws =>
    let s := liftState ws
    let v := s.p / mass
    let F := law.eval s.q s.p v
    let new : State :=
      {
        q := s.q + dt * v,
        p := s.p + dt * F
      }
    lowerState new
  name := "discovered-law"
}

/-
============================================================
統合世界モデル
============================================================
-/

structure UnifiedApexModel (n : Nat) where
  discrete : WorldState n
  regression : RegressionData
  candidates : List LawExpr
  selected : Option LawExpr
  dt : Scalar
  mass : Scalar

def UnifiedApexModel.build
    {n : Nat}
    (dt mass : Scalar)
    (ws : WorldState n)
    (traj : Trajectory)
    (depth : Nat)
    (λ : Scalar) :
    UnifiedApexModel n :=
  let reg := makeRegressionData dt traj
  let cands := generate depth
  let sel := selectBest cands reg mass λ
  {
    discrete := ws,
    regression := reg,
    candidates := cands,
    selected := sel,
    dt := dt,
    mass := mass
  }

/-
============================================================
離散世界の進化（発見された物理法則で更新）
============================================================
-/

def UnifiedApexModel.step
    {n : Nat}
    (U : UnifiedApexModel n) :
    UnifiedApexModel n :=
  match U.selected with
  | none => U
  | some law =>
      let phys := lawToPhysics U.dt U.mass law
      {
        U with
        discrete := phys.evolve U.discrete
      }
