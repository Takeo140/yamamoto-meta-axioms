-- License Apache 2.0  Takeo Yamamoto
namespace UHA.Protocol

abbrev U64 := UInt64

structure CTerm where
  index : UInt64
  value : U64
  deriving Repr, BEq

structure UHAPacket where
  n : Nat
  terms : List CTerm
  deriving Repr, BEq

/-- UInt64 を 8 バイトのリストにする（リトルエンディアン） -/
def encodeU64 (x : UInt64) : List UInt8 :=
  List.range 8 |>.map (fun i => 
    UInt8.ofNat ((x.shiftRight (8*i)).toNat % 256))

/-- UInt64 を 8 バイトから復元 -/
def decodeU64 : List UInt8 → Option UInt64
| bytes =>
  if h : bytes.length = 8 then
    some <| List.foldl
      (fun acc (p : UInt8 × Nat) =>
        acc + (UInt64.ofNat p.fst.toNat).shiftLeft (8*p.snd))
      0
      (bytes.zip (List.range 8))
  else
    none

/-- CTerm のエンコード -/
def encodeCTerm (t : CTerm) : List UInt8 :=
  encodeU64 t.index ++ encodeU64 t.value

/-- CTerm のデコード -/
def decodeCTerm : List UInt8 → Option (CTerm × List UInt8)
| bytes =>
  do
    let idxBytes ← bytes.take? 8
    let valBytes ← bytes.drop? 8 >>= fun b => b.take? 8
    let rest ← bytes.drop? 16
    let idx ← decodeU64 idxBytes
    let val ← decodeU64 valBytes
    pure (⟨idx, val⟩, rest)

/-- パケットのエンコード -/
def encode (pkt : UHAPacket) : List UInt8 :=
  encodeU64 (UInt64.ofNat pkt.n)
  ++ encodeU64 (UInt64.ofNat pkt.terms.length)
  ++ pkt.terms.bind encodeCTerm

/-- パケットのデコード -/
def decode : List UInt8 → Option UHAPacket
| bytes =>
  do
    let nBytes ← bytes.take? 8
    let lenBytes ← bytes.drop? 8 >>= fun b => b.take? 8
    let rest ← bytes.drop? 16
    let n ← decodeU64 nBytes
    let len ← decodeU64 lenBytes
    let rec loop : Nat → List UInt8 → Option (List CTerm × List UInt8)
    | 0, bs => some ([], bs)
    | Nat.succ k, bs =>
      do
        let (t, bs') ← decodeCTerm bs
        let (ts, bs'') ← loop k bs'
        pure (t :: ts, bs'')
    let (ts, _) ← loop len.toNat rest
    pure ⟨n.toNat, ts⟩

/-- 完全性の証明：decode ∘ encode = id -/
theorem decode_encode_inverse (pkt : UHAPacket) :
  decode (encode pkt) = some pkt := by
  unfold decode encode
  -- この証明は実装の詳細によって異なります
  -- 以下のアプローチを試してください：
  sorry

end UHA.Protocol
