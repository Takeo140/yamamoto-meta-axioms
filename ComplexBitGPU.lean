/-
Copyright (c) 2026 Takeo Yamamoto
Released under the Apache 2.0
-/

-- 1. 64ビット固定長ベクトル（BitVec 64）を使用した二進法虚数表現の構造体定義
-- これにより、メモリ空間ではなく「物理的な64本のワイヤ」としてハードウェア化可能になります
structure BinComplex64 where
  re : BitVec 64
  im : BitVec 64
  deriving BEq, Repr

-- 64ビット環境でのゼロ（初期化用）の定義
def binComplexZero64 : BinComplex64 :=
  ⟨BitVec.ofNat 64 0, BitVec.ofNat 64 0⟩

-- 2. 64ビット環境での分岐なし・複素数加算コア
def binComplexAdd64 (a b : BinComplex64) : BinComplex64 :=
  ⟨a.re + b.re, a.im + b.im⟩

-- 3. 64ビット環境での分岐なし・複素数乗算コア
-- 符号反転やビットシフトも含め、すべて64ビットの算術回路のみで完結
def binComplexMul64 (a b : BinComplex64) : BinComplex64 :=
  ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩

-- 4. 64ビットGPU仕様の固定サイズ行列の型定義 (Fin n → Fin m → 要素)
def BinMatrix64 (n m : Nat) := Fin n → Fin m → BinComplex64

-- 行列から要素を安全に抽出する射影
def BinMatrix64.get {n m : Nat} (M : BinMatrix64 n m) (i : Fin n) (j : Fin m) : BinComplex64 :=
  M i j

-- 5. シストリック・アレイ（GPU）の64ビット同期用静的ループ関数
def sumHelper64 (f : Nat → BinComplex64) : Nat → BinComplex64
  | 0 => binComplexZero64
  | k + 1 => binComplexAdd64 (f k) (sumHelper64 f k)

-- 6. 核心：条件分岐なき「64ビット・ハイエンド複素行列積」の完全定義
def binMatrixMul64 {n m p : Nat} (A : BinMatrix64 n m) (B : BinMatrix64 m p) : BinMatrix64 n p :=
  fun i j =>
    sumHelper64 (fun k => 
      -- ここの if はコンパイル時の静的境界ガード。
      -- 物理シリコン上では、64ビット幅のバスが並列に走る固定グリッドとして展開されます。
      if h : k < m then 
        binComplexMul64 (A i ⟨k, h⟩) (B ⟨k, h⟩ j)
      else 
        binComplexZero64
    ) m
