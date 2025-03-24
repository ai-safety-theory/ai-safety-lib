import Mathlib.Order.Basic

namespace GameTheory

class Preference (α : Type*) extends Preorder α where
  (total : ∀ a b : α, a ≤ b ∨ b ≤ a)

abbrev JointStrategy (Player : Type) (Strategy : Player → Type) :=
  (p : Player) → Strategy p

structure Game where
  Player : Type                                      -- Type representing players
  [decidableEq : DecidableEq Player]                 -- Player equality is decidable
  Strategy : Player → Type                           -- Strategies available to each player
  JointPreference : Player → Preference (JointStrategy Player Strategy)  -- Joint preferences over joint strategies

def unilateral_deviation (g : Game) [inst : DecidableEq g.Player]
    (s : JointStrategy g.Player g.Strategy) (p : g.Player) (new_strat : g.Strategy p) : JointStrategy g.Player g.Strategy :=
  fun p' => if h : p' = p then by rw [h]; exact new_strat else s p'

def is_nash_equilibrium (g : Game) [DecidableEq g.Player] (s : JointStrategy g.Player g.Strategy) : Prop :=
  ∀ (p : g.Player) (s' : g.Strategy p),
    (g.JointPreference p).le s (unilateral_deviation g s p s')

end GameTheory
