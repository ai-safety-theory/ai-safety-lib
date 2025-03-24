import AiSafetyLib.GameTheory.GameTheory

open GameTheory

namespace Preferences

def utility {Player : Type} {Strategy : Player → Type} {α : Type} [Preference α]
    (u : JointStrategy Player Strategy → α)
    (s : JointStrategy Player Strategy) : α :=
  u s

def preference_from_utility {Player : Type} {Strategy : Player → Type} {α : Type}
    [Preference α] (u : JointStrategy Player Strategy → α) : Preference (JointStrategy Player Strategy) where
  le := fun x y => u x ≤ u y
  le_refl := fun x => Preorder.le_refl (u x)
  le_trans := fun x y z h1 h2 => @Preorder.le_trans α _ (u x) (u y) (u z) h1 h2
  total := fun x y => Preference.total (u x) (u y)

instance : Preference Int where
  le := (· ≤ ·)
  le_refl := @Int.le_refl
  le_trans := @Int.le_trans
  total := @Int.le_total
  lt_iff_le_not_le := @Int.lt_iff_le_not_le

end Preferences
