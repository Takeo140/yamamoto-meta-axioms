License Apache 2.0 Takeo Yamamoto
import Std.Data.List.Basic
import Std.Data.List.Lemmas

namespace TakeoStream

/-- Event：値とメタ情報（辞書）を持つ最小構造 -/
structure Event (α : Type) :=
  (value : α)
  (meta  : Std.HashMap String String := {})

/-- Stream：Event の有限列。静かな構造。 -/
structure Stream (α : Type) :=
  (events : List (Event α))

namespace Stream

/-- map：値にだけ変化を与える最小限の操作 -/
def map {α β : Type} (f : α → β) (s : Stream α) : Stream β :=
  ⟨s.events.map (fun e => Event.mk (f e.value) e.meta)⟩

/-- filter：述語に合う Event だけを残す静かな選別 -/
def filter {α : Type} (p : α → Bool) (s : Stream α) : Stream α :=
  ⟨s.events.filter (fun e => p e.value)⟩

/-- reduce：モノイド的畳み込み。反復と変化の最小単位。 -/
def reduce {α β : Type} (f : β → α → β) (init : β) (s : Stream α) : β :=
  s.events.foldl (fun acc e => f acc e.value) init

/-- toList：内部構造をそのまま返すだけの簡素な API -/
def toList {α : Type} (s : Stream α) : List (Event α) :=
  s.events

end Stream

/-- map の合成律：Quiet Architecture の代数的性質 -/
theorem map_comp {α β γ : Type}
    (f : α → β) (g : β → γ) (s : Stream α) :
    Stream.map g (Stream.map f s)
      = Stream.map (fun x => g (f x)) s := by
  cases s
  simp [Stream.map, List.map_map]

/-- filter の合成律：述語の論理積に対応 -/
theorem filter_and {α : Type}
    (p q : α → Bool) (s : Stream α) :
    Stream.filter q (Stream.filter p s)
      = Stream.filter (fun x => p x && q x) s := by
  cases s
  simp [Stream.filter, List.filter_filter]

end TakeoStream
