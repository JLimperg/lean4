-- FIXME doc everywhere

namespace Lean

inductive UniqueIdClass
  | default
  | pp
  | synthInstance
  | widgetDiag
  | worker

@[inline_if_reduce] def UniqueIdClass.index : UniqueIdClass → UInt8
  | default => 0
  | pp => 1
  | synthInstance => 2
  | widgetDiag => 3
  | worker => 4

structure UniqueId where
  id : UInt64
  deriving Inhabited, BEq, Hashable

namespace UniqueId

instance : LT UniqueId where
  lt x y := x.id < y.id

instance : DecidableRel ((· < ·) : UniqueId → UniqueId → _) :=
  λ x y => inferInstanceAs (Decidable (x.id < y.id))

instance : LE UniqueId where
  le x y := x.id ≤ y.id

instance : DecidableRel ((· ≤ ·) : UniqueId → UniqueId → _) :=
  λ x y => inferInstanceAs (Decidable (x.id ≤ y.id))

instance : Ord UniqueId where
  compare x y := compare x.id y.id

instance : ToString UniqueId where
  toString x := toString x.id

instance : Repr UniqueId where
  reprPrec x p := reprPrec x.id p

@[inline] protected def succ (i : UniqueId) : UniqueId :=
  ⟨i.id + 1⟩

@[inline] protected def toNat (i : UniqueId) : Nat :=
  i.id.toNat

@[inline] protected def ofNat (n : Nat) : UniqueId :=
  ⟨.ofNat n⟩

def toNameWithPrefix (i : UniqueId) («prefix» : Name) : Name :=
  .num «prefix» i.toNat

end UniqueId

@[inline] private def uInt8ToUInt64 (x : UInt8) : UInt64 :=
  ⟨⟨x.val.val, Nat.lt_trans x.val.isLt (by decide)⟩⟩

@[inline] def UniqueIdClass.firstUniqueId (cls : UniqueIdClass) : UniqueId :=
  ⟨(uInt8ToUInt64 cls.index <<< 56) + 1⟩

structure UniqueIdGenerator where
  idx : UniqueId
  deriving Inhabited

@[inline] def mkUniqueIdGenerator (cls : UniqueIdClass) : UniqueIdGenerator where
  idx := cls.firstUniqueId

namespace UniqueIdGenerator

@[inline] def curr (g : UniqueIdGenerator) : UniqueId :=
  g.idx

@[inline] def next (g : UniqueIdGenerator) : UniqueIdGenerator :=
  { g with idx := g.idx.succ }

end UniqueIdGenerator

class MonadUniqueIdGenerator (m : Type → Type) where
  getNGen : m UniqueIdGenerator
  setNGen : UniqueIdGenerator → m Unit

export MonadUniqueIdGenerator (getNGen setNGen)

def mkUniqueId {m : Type → Type} [Monad m] [MonadUniqueIdGenerator m] : m UniqueId := do
  let ngen ← getNGen
  let r := ngen.curr
  setNGen ngen.next
  pure r

instance monadUniqueIdGeneratorLift (m n : Type → Type) [MonadLift m n] [MonadUniqueIdGenerator m] : MonadUniqueIdGenerator n := {
  getNGen := liftM (getNGen : m _),
  setNGen := fun ngen => liftM (setNGen ngen : m _)
}

end Lean
