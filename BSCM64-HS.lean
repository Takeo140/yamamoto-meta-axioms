-- Author: Takeo Yamamoto
-- License: CC BY 4.0
import Mathlib.Data.Nat.Basic

/-!
# Bounded Smooth Collatz Machine (BSCM) — High-Speed Execution Version
# Optimized with UInt64, Bitwise Operations, and Arrays
-/

-- ───────────────────────────────────────────────────────────────────
-- 1. 実行用 高速遷移関数
-- ───────────────────────────────────────────────────────────────────

/-- 
偶数判定をビットマスク(s &&& 1)で、除算を右シフト(>>> 1)で行う。
奇数の場合の (s + 1) / 2 は、オーバーフロー回避のため (s >>> 1) + 1 と等価変換。
-/
@[inline]
def bscm_delta_fast (s : UInt64) : UInt64 :=
  if (s &&& 1) == 0 then
    s >>> 1
  else
    (s >>> 1) + 1

-- ───────────────────────────────────────────────────────────────────
-- 2. 実行用 コントロールインターフェース
-- ───────────────────────────────────────────────────────────────────

/--
UInt64の加算は自動的に 2^64 (18446744073709551616) のモジュロ演算となるため、
高コストな除算 `%` を完全に省略できる。
-/
@[inline]
def bscm_control_step_fast (current_state : UInt64) (external_input : UInt64) : UInt64 :=
  bscm_delta_fast (current_state + external_input)

/--
List (リンクリスト) ではなく Array (連続メモリ) を使用し、
キャッシュミスを防ぐ。末尾再帰は foldl に委譲し、ネイティブなループ処理にコンパイルさせる。
-/
def bscm_control_exec_fast (initial_state : UInt64) (inputs : Array UInt64) : UInt64 :=
  inputs.foldl bscm_control_step_fast initial_state
