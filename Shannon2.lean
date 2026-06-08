/-!
# Shannon Coding (64-bit Optimized)
Copyright (c) 2026 Takeo Yamamoto
License: Apache License 2.0
-/

import Std.Data.UInt64

/--
Shannon符号における符号長計算: l_i = ceil(-log2(p_i))
64bit整数内の最上位ビット位置(CLZ)を利用して定数時間で算出。
-/
def shannon_len (p : UInt64) : UInt64 :=
  -- p を正規化し、ビット長を算出する論理
  -- 63 - (p の最上位ビットのインデックス)
  64 - (64 - (p.leadingZeros).toUInt64)

/--
Shannon符号の生成:
累積確率を符号長分だけ右シフトすることで、一意のビット列を抽出する。
-/
def encode_shannon (cum_prob : UInt64) (len : UInt64) : UInt64 :=
  cum_prob >>> (64 - len)
