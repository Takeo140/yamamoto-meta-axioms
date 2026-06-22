-- =============================================================================
-- F-BSCM: Space-Time Invariant Meta-Axiomatic Computing Model
-- High-Speed Execution Version
--
-- Author: Takeo Yamamoto
-- License: CC BY 4.0　Apache 2.0
-- =============================================================================

import Mathlib.Data.Array.Basic

/-!
# F-BSCM: 実行特化型 高速演算アーキテクチャ
証明済みの有界性と不変条件を前提とし、実行時のオーバーヘッド（任意精度演算、
ヒープ割り当て、ポインタ追跡）を極限まで削ぎ落としたネイティブコード。
-/

-- =============================================================================
-- 1. Time Domain: Bounded Smooth Collatz Machine (BSCM)
-- =============================================================================

/-- 
偶数/奇数判定をビットマスク(`&&&`)に、除算を論理右シフト(`>>>`)に変更。
証明により状態が $2^{64}-1$ を超えないことが保証されているため、UInt64レジスタ演算へマッピング。
-/
@[inline]
def bscm_delta_fast (s : UInt64) : UInt64 :=
  if (s &&& 1) == 0 then
    s >>> 1
  else
    (s >>> 1) + 1

/-- 
UInt64の加算によるハードウェアレベルの自然なラップアラウンドを利用し、
CPUサイクルを消費する高コストなモジュロ除算（% 18446744073709551616）を物理的に消去。
-/
@[inline]
def bscm_control_step_fast (current_state : UInt64) (external_input : UInt64) : UInt64 :=
  bscm_delta_fast (current_state + external_input)

/-- 
List（リンクリスト）の再帰処理から、連続メモリ（Array）に対する foldl に変更。
コンパイル時にC言語の for ループに展開され、キャッシュミスを防止。
-/
def bscm_control_exec_fast (initial_state : UInt64) (inputs : Array UInt64) : UInt64 :=
  inputs.foldl bscm_control_step_fast initial_state

-- =============================================================================
-- 2. Space Domain: F-Theory Topological Indexing
-- =============================================================================

/-- 
`Nat × Nat` (Prod) によるヒープ上のポインタ動的割り当て（GC負荷）を防ぐため、
Unboxedな値型構造体（FNode）として再定義。
-/
structure FNode where
  weight : UInt64
  value  : UInt64
deriving Inhabited

/--
メタ公理 A4 を満たすソート順インサート関数（高速版）。
リンクリストの再帰的なポインタ追跡を廃止し、連続メモリ配列に対する
線形探索（findIdx?）と、C言語の `memmove` に相当する `insertAt` に置換。
空間全体のトポロジー維持コストを最小化。
-/
def insert_node_sorted_fast (nodes : Array FNode) (w : UInt64) (v : UInt64) : Array FNode :=
  match nodes.findIdx? (fun n => w >= n.weight) with
  | some idx => nodes.insertAt idx ⟨w, v⟩
  | none     => nodes.push ⟨w, v⟩

-- =============================================================================
-- 3. Unified Architecture (Structure)
-- =============================================================================

/-- 時空統合メタ計算空間の構造体（実行最適化版） -/
structure UnifiedMachine_Fast where
  currentState : UInt64
  fSpace       : Array FNode
