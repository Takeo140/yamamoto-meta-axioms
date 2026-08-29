License Apache 2.0  Takeo Yamamoto
/-
  Clifford+T の完全再構成：
  1. Zom = Z[ω]
  2. GC = Z[ω][1/√2]
  3. CMat/CVec = GC 行列
  4. CBitPhase = 古典ビット × 位相（GC）
  5. Clifford+T ゲートを「値操作＋位相操作」として再構成
-/

import Mathlib.Tactic.Ring

namespace CliffordT_Reconstructed

--------------------------------------------------------------------------------
-- 1. Zom = Z[ω], ω⁴ = -1
--------------------------------------------------------------------------------

structure Zom where
  a b c d : Int
deriving DecidableEq, Repr

namespace Zom

def zero : Zom := ⟨0,0,0,0⟩
def one  : Zom := ⟨1,0,0,0⟩
def omega : Zom := ⟨0,1,0,0⟩
def imUnit : Zom := ⟨0,0,1,0⟩

def add (x y : Zom) : Zom := ⟨x.a+y.a, x.b+y.b, x.c+y.c, x.d+y.d⟩
def neg (x : Zom) : Zom := ⟨-x.a, -x.b, -x.c, -x.d⟩
def sub (x y : Zom) := add x (neg y)

/-- ω⁴ = -1 を使って還元した積 -/
def mul (x y : Zom) : Zom :=
  ⟨ x.a*y.a - x.b*y.d - x.c*y.c - x.d*y.b
  , x.a*y.b + x.b*y.a - x.c*y.d - x.d*y.c
  , x.a*y.c + x.b*y.b + x.c*y.a - x.d*y.d
  , x.a*y.d + x.b*y.c + x.c*y.b + x.d*y.a ⟩

def conj (x : Zom) : Zom := ⟨x.a, -x.d, -x.c, -x.b⟩

end Zom

--------------------------------------------------------------------------------
-- 2. GC = Z[ω][1/√2]
--------------------------------------------------------------------------------

def Zom.sqrt2 : Zom := ⟨0,1,0,-1⟩

def Zom.sqrt2Pow : Nat → Zom
  | 0 => Zom.one
  | n+1 => Zom.mul Zom.sqrt2 (Zom.sqrt2Pow n)

structure GC where
  num : Zom
  k   : Nat
deriving DecidableEq, Repr

namespace GC

def zero : GC := ⟨Zom.zero, 0⟩
def one  : GC := ⟨Zom.one, 0⟩

def add (x y : GC) : GC :=
  let m := max x.k y.k
  ⟨ Zom.add (Zom.mul x.num (Zom.sqrt2Pow (m - x.k)))
            (Zom.mul y.num (Zom.sqrt2Pow (m - y.k))),
    m ⟩

def neg (x : GC) : GC := ⟨Zom.neg x.num, x.k⟩
def sub (x y : GC) := add x (neg y)
def mul (x y : GC) : GC := ⟨Zom.mul x.num y.num, x.k + y.k⟩
def conj (x : GC) : GC := ⟨Zom.conj x.num, x.k⟩

end GC

--------------------------------------------------------------------------------
-- 3. CMat / CVec
--------------------------------------------------------------------------------

abbrev CVec := Array GC
abbrev CMat := Array (Array GC)

namespace CMat

def rows (m : CMat) := m.size
def cols (m : CMat) := (m.get! 0).size
def get (m : CMat) (r c : Nat) := (m.get! r).get! c

def identity (n : Nat) : CMat :=
  Array.ofFn (fun i : Fin n =>
    Array.ofFn (fun j : Fin n =>
      if i.val = j.val then GC.one else GC.zero))

def dagger (m : CMat) : CMat :=
  Array.ofFn (fun j : Fin m.cols =>
    Array.ofFn (fun i : Fin m.rows =>
      GC.conj (m.get i j)))

def matMul (a b : CMat) : CMat :=
  Array.ofFn (fun i : Fin a.rows =>
    Array.ofFn (fun j : Fin b.cols =>
      (List.range a.cols).foldl
        (fun acc k => GC.add acc (GC.mul (a.get i k) (b.get k j)))
        GC.zero))

end CMat

--------------------------------------------------------------------------------
-- 4. 古典ビット × 位相（GC）
--------------------------------------------------------------------------------

structure CBitPhase where
  bit   : Bool
  phase : GC
deriving Repr

def embedBit (b : Bool) : GC :=
  if b then GC.one else GC.zero

def applyPhase (p : GC) (x : CBitPhase) : CBitPhase :=
  { bit := x.bit, phase := GC.mul p x.phase }

--------------------------------------------------------------------------------
-- 5. Clifford+T の完全再構成（値操作＋位相操作）
--------------------------------------------------------------------------------

-- Z：値は変えず、位相に -1 を掛ける
def gateZ' (x : CBitPhase) : CBitPhase :=
  applyPhase ⟨Zom.neg Zom.one, 0⟩ x

-- S：値は変えず、位相に i を掛ける
def gateS' (x : CBitPhase) : CBitPhase :=
  applyPhase ⟨Zom.imUnit, 0⟩ x

-- T：値は変えず、位相に ω を掛ける
def gateT' (x : CBitPhase) : CBitPhase :=
  applyPhase ⟨Zom.omega, 0⟩ x

-- X：値だけ反転する
def gateX' (x : CBitPhase) : CBitPhase :=
  { bit := not x.bit, phase := x.phase }

-- CNOT：制御ビットが 1 のとき、ターゲットの値を反転
def gateCNOT' (c t : CBitPhase) : CBitPhase × CBitPhase :=
  if c.bit then
    (c, { bit := not t.bit, phase := t.phase })
  else
    (c, t)

-- H：唯一「値と位相を混ぜる」特異点
def gateH' (x : CBitPhase) : CBitPhase :=
  if x.bit then
    { bit := false, phase := ⟨Zom.one, 1⟩ }  -- 1/√2
  else
    { bit := true,  phase := ⟨Zom.one, 1⟩ }

end CliffordT_Reconstructed
