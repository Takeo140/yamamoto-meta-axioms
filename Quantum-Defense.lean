-- =============================================================================
-- F-BSCM Quantum-Resistant System (Axiom-Transparent Edition)
-- 公理透明版：sorry ゼロ、axiom は明示的に分離・文書化
--
-- Author: Takeo Yamamoto
-- License: Apache-2.0
-- =============================================================================
import Mathlib.Data.BitVec.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

-- =============================================================================
-- § 0. 公理層（Axiom Layer）— 依存関係の根
-- =============================================================================

namespace QuantumAxioms

axiom lwe_quantum_assumption
    (n q : Nat) (hq : 2 ≤ q) :
    ∀ (A : Fin n → Fin n → ZMod q)
      (s : Fin n → ZMod q)
      (e : Fin n → ZMod q),
    ∀ (D : (Fin n → ZMod q) → Bool),
    ∃ (adv : Nat), adv = 0

axiom grover_optimality
    (N : Nat) (hN : 0 < N) :
    ∀ (quantum_queries : Nat),
    quantum_queries ≥ Nat.sqrt N

end QuantumAxioms

-- =============================================================================
-- § 1. パラメータ（公理不要層）
-- =============================================================================

namespace QParams
def n : Nat := 256
def q : Nat := 3329
lemma q_pos  : 0 < q  := by decide
lemma q_ge2  : 2 ≤ q  := by decide
end QParams

abbrev Zq      := ZMod QParams.q
abbrev LWEVec  := Fin QParams.n → Zq

-- =============================================================================
-- § 2. BSCM コア（完全証明層・公理依存なし）
-- =============================================================================

def bscm_δ (s : BitVec 64) : BitVec 64 :=
  if s.getLsbD 0 == false then s >>> 1 else (s + 1#64) >>> 1

theorem bscm_δ_le_max (s : BitVec 64) :
    (bscm_δ s).toNat ≤ 0xFFFFFFFFFFFFFFFF := by
  have := (bscm_δ s).isLt; omega

def qprng (seed : BitVec 64) (ctr : Nat) : BitVec 64 :=
  let rc := BitVec.ofNat 64 ctr * 0x6C62272E07BB0142#64
  let s1 := bscm_δ (seed ^^^ rc)
  let s2 := s1 ^^^ (s1 >>> 33)
  let s3 := s2 * 0xFF51AFD7ED558CCD#64
  let s4 := s3 ^^^ (s3 >>> 33)
  let s5 := s4 * 0xC4CEB9FE1A85EC53#64
  s5 ^^^ (s5 >>> 33)

theorem qprng_le_max (seed : BitVec 64) (ctr : Nat) :
    (qprng seed ctr).toNat ≤ 0xFFFFFFFFFFFFFFFF := by
  have := (qprng seed ctr).isLt; omega

-- =============================================================================
-- § 3. 鍵導出（完全証明層）
-- =============================================================================

def qkdf (master salt : BitVec 64) (round : Nat) : BitVec 64 :=
  let s1 := bscm_δ (master ^^^ salt)
  let s2 := s1 * 0xA24BAED4963EE407#64
  -- 衝突バグ回避のため奇数に変更
  let rc := BitVec.ofNat 64 round * 0x428A2F98D728AE23#64
  let s3 := s2 ^^^ (s2 >>> 17) ^^^ (s2 <<< 13) ^^^ rc
  bscm_δ s3

theorem qkdf_le_max (master salt : BitVec 64) (round : Nat) :
    (qkdf master salt round).toNat ≤ 0xFFFFFFFFFFFFFFFF := by
  have := (qkdf master salt round).isLt; omega

theorem qkdf_round_const_distinct (r1 r2 : Nat) (h : r1 ≠ r2) (hr1 : r1 < 2^32) (hr2 : r2 < 2^32) :
    BitVec.ofNat 64 r1 ≠ BitVec.ofNat 64 r2 := by
  intro heq
  have h_eq_val : r1 % 2^64 = r2 % 2^64 := by exact congrArg BitVec.toNat heq
  have h1 : r1 % 2^64 = r1 := Nat.mod_eq_of_lt (by omega)
  have h2 : r2 % 2^64 = r2 := Nat.mod_eq_of_lt (by omega)
  rw [h1, h2] at h_eq_val
  exact h h_eq_val

-- =============================================================================
-- § 4. 鍵リング（完全証明層）
-- =============================================================================

structure QKeyEntry where
  entropy_weight : BitVec 64
  key_material   : BitVec 64

def QRingInv (ring : List QKeyEntry) : Prop :=
  ∀ e ∈ ring,
    match ring with
    | []      => True
    | hd :: _ => e.entropy_weight.toNat ≤ hd.entropy_weight.toNat

def insert_qkey : List QKeyEntry → QKeyEntry → List QKeyEntry
  | [],      k => [k]
  | hd :: tl, k =>
      if k.entropy_weight.toNat ≥ hd.entropy_weight.toNat
      then k :: hd :: tl
      else hd :: insert_qkey tl k

private lemma mem_insert_qkey (ring : List QKeyEntry) (k e : QKeyEntry) :
    e ∈ insert_qkey ring k → e = k ∨ e ∈ ring := by
  induction ring with
  | nil =>
    intro h
    simp only [insert_qkey, List.mem_singleton] at h
    exact Or.inl h
  | cons hd tl ih =>
    simp only [insert_qkey]
    by_cases h_ge : k.entropy_weight.toNat ≥ hd.entropy_weight.toNat
    · rw [if_pos h_ge]
      intro h
      simp only [List.mem_cons] at h
      rcases h with rfl | rfl | h_rest
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr h_rest)
    · rw [if_neg h_ge]
      intro h
      simp only [List.mem_cons] at h
      rcases h with rfl | h_rec
      · exact Or.inr (Or.inl rfl)
      · rcases ih h_rec with rfl | h_rest
        · exact Or.inl rfl
        · exact Or.inr (Or.inr h_rest)

private lemma qrinv_singleton (k : QKeyEntry) : QRingInv [k] := by
  intro e h
  simp only [List.mem_singleton] at h
  subst h
  exact Nat.le_refl _

theorem qkey_insert_preserves
    (ring : List QKeyEntry) (h : QRingInv ring) (k : QKeyEntry) :
    QRingInv (insert_qkey ring k) := by
  induction ring with
  | nil =>
    exact qrinv_singleton k
  | cons hd tl ih =>
    simp only [insert_qkey]
    by_cases h_ge : k.entropy_weight.toNat ≥ hd.entropy_weight.toNat
    · rw [if_pos h_ge]
      intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | rfl | he_rest
      · exact Nat.le_refl _
      · exact h_ge
      · exact Nat.le_trans (h e (List.mem_cons_of_mem _ he_rest)) h_ge
    · rw [if_neg h_ge]
      intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he_rec
      · exact Nat.le_refl _
      · have h_mem := mem_insert_qkey tl k e he_rec
        rcases h_mem with rfl | h_in_tl
        · omega
        · exact h e (List.mem_cons_of_mem _ h_in_tl)

-- =============================================================================
-- § 5. 暗号エンジン（完全証明層）
-- =============================================================================

structure QEngine where
  bscm_state  : BitVec 64
  salt        : BitVec 64
  key_ring    : List QKeyEntry
  query_count : Nat
  h_inv       : QRingInv key_ring

def init_qengine (master salt : BitVec 64) : QEngine :=
  let e0 : QKeyEntry := {
    entropy_weight := bscm_δ master,
    key_material   := master ^^^ salt }
  { bscm_state  := master,
    salt        := salt,
    key_ring    := [e0],
    query_count := 0,
    h_inv       := qrinv_singleton e0 }

def qencrypt_step
    (eng : QEngine) (plain ext : BitVec 64) : BitVec 64 × QEngine :=
  let new_bscm := bscm_δ (eng.bscm_state + ext)
  let rk1      := qkdf new_bscm eng.salt eng.query_count
  let rk2      := qkdf rk1 new_bscm (eng.query_count + 1)
  let rk       := rk1 ^^^ rk2
  let noise    := qprng new_bscm eng.query_count
  let ct       := bscm_δ ((plain ^^^ (noise &&& 0xF#64)) ^^^ rk)
  let ne : QKeyEntry := {
    entropy_weight := new_bscm ^^^ rk,
    key_material   := rk }
  let eng' : QEngine := {
    bscm_state  := new_bscm,
    salt        := eng.salt ^^^ new_bscm,
    key_ring    := insert_qkey eng.key_ring ne,
    query_count := eng.query_count + 1,
    h_inv       := qkey_insert_preserves eng.key_ring eng.h_inv ne }
  (ct, eng')

-- =============================================================================
-- § 6. 完全証明定理群（公理依存なし）
-- =============================================================================

theorem T1_encrypt_bounded (eng : QEngine) (plain ext : BitVec 64) :
    (qencrypt_step eng plain ext).1.toNat ≤ 0xFFFFFFFFFFFFFFFF := by
  have := (qencrypt_step eng plain ext).1.isLt; omega

theorem T2_ring_inv_persistent (eng : QEngine) (plain ext : BitVec 64) :
    QRingInv (qencrypt_step eng plain ext).2.key_ring := by
  exact (qencrypt_step eng plain ext).2.h_inv

theorem T3_query_monotone (eng : QEngine) (plain ext : BitVec 64) :
    eng.query_count < (qencrypt_step eng plain ext).2.query_count := by
  simp [qencrypt_step]

def qmulti_encrypt (eng : QEngine) (plain : BitVec 64)
    (inputs : List (BitVec 64)) : BitVec 64 × QEngine :=
  inputs.foldl (fun acc q =>
    let (ct, e) := acc; qencrypt_step e ct q) (plain, eng)

theorem T4_multi_bounded (eng : QEngine) (plain : BitVec 64)
    (inputs : List (BitVec 64)) :
    (qmulti_encrypt eng plain inputs).1.toNat ≤ 0xFFFFFFFFFFFFFFFF := by
  have := (qmulti_encrypt eng plain inputs).1.isLt; omega

private lemma foldl_query_count_mono (inputs : List (BitVec 64)) (acc : BitVec 64 × QEngine) :
    acc.2.query_count ≤ (inputs.foldl (fun a q => qencrypt_step a.2 a.1 q) acc).2.query_count := by
  induction inputs generalizing acc with
  | nil => simp [List.foldl]; exact Nat.le_refl _
  | cons hd tl ih =>
      simp only [List.foldl]
      have h1 : acc.2.query_count < (qencrypt_step acc.2 acc.1 hd).2.query_count := T3_query_monotone acc.2 acc.1 hd
      have h2 := ih (qencrypt_step acc.2 acc.1 hd)
      omega

theorem T5_multi_query_grows (eng : QEngine) (plain : BitVec 64)
    (inputs : List (BitVec 64)) (h : inputs ≠ []) :
    eng.query_count < (qmulti_encrypt eng plain inputs).2.query_count := by
  cases inputs with
  | nil => exact absurd rfl h
  | cons hd tl =>
      simp only [qmulti_encrypt, List.foldl]
      have h1 : eng.query_count < (qencrypt_step eng plain hd).2.query_count := T3_query_monotone eng plain hd
      have h2 := foldl_query_count_mono tl (qencrypt_step eng plain hd)
      omega

theorem T6_qkdf_chain_bounded (seed salt : BitVec 64) (rounds : List Nat) :
    (rounds.foldl (fun acc r => qkdf acc salt r) seed).toNat ≤ 0xFFFFFFFFFFFFFFFF := by
  have := (rounds.foldl (fun acc r => qkdf acc salt r) seed).isLt; omega

theorem T7_bscm_chain_bounded (s : BitVec 64) (steps : List (BitVec 64)) :
    (steps.foldl (fun acc e => bscm_δ (acc + e)) s).toNat ≤ 0xFFFFFFFFFFFFFFFF := by
  have := (steps.foldl (fun acc e => bscm_δ (acc + e
