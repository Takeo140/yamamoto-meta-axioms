/-
Copyright (c) 2026 Takeo Yamamoto
Released under the Apache 2.0
-/

-- 1. 二進法虚数表現の構造体定義（実数部と虚数部の並列保持）
structure BinComplex where
  re : Int
  im : Int
  deriving BEq, Repr

-- ゼロ（初期化用）の定義
def binComplexZero : BinComplex := ⟨0, 0⟩

-- 2. 分岐なしの複素数加算コア
def binComplexAdd (a b : BinComplex) : BinComplex :=
  ⟨a.re + b.re, a.im + b.im⟩

-- 3. 分岐なしの複素数乗算コア（符号反転も含めて純粋な算術のみで完結）
def binComplexMul (a b : BinComplex) : BinComplex :=
  ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩

-- 4. GPU仕様の固定サイズ行列の型定義 (Fin n → Fin m → 要素)
def BinMatrix (n m : Nat) := Fin n → Fin m → BinComplex

-- 行列から要素を安全に抽出する射影
def BinMatrix.get {n m : Nat} (M : BinMatrix n m) (i : Fin n) (j : Fin m) : BinComplex :=
  M i j

-- 5. シストリック・アレイ（GPU）の畳み込みを再現するための静的ループ関数
-- 0 から k-1 までの要素を分岐なしで累積加算する
def sumHelper (f : Nat → BinComplex) : Nat → BinComplex
  | 0 => binComplexZero
  | k + 1 => binComplexAdd (f k) (sumHelper f k)

-- 6. 核心：条件分岐なき「GPU仕様・複素行列積」の完全定義
def binMatrixMul {n m p : Nat} (A : BinMatrix n m) (B : BinMatrix m p) : BinMatrix n p :=
  fun i j =>
    sumHelper (fun k => 
      -- ここの if は型安全（Fin m の境界内であること）をコンパイラに示すための静的ガード。
      -- 実際の回路では、サイズ m の物理的なグリッド配線として展開されるため、実行時の分岐は発生しません。
      if h : k < m then 
        binComplexMul (A i ⟨k, h⟩) (B ⟨k, h⟩ j)
      else 
        binComplexZero
    ) m
