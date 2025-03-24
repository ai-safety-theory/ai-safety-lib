import Mathlib.Tactic
import Mathlib.Tactic.Basic
import AiSafetyLib.GameTheory.GameTheory
import AiSafetyLib.GameTheory.Preferences

open GameTheory
open Preferences

--TODO: Use mixed strategies, expected utility

inductive PDPlayer
  | Alice
  | Bob
  deriving DecidableEq

inductive PDStrategy
  | Cooperate
  | Defect

def prisoner_utility (p : PDPlayer) (s : JointStrategy PDPlayer (fun _ => PDStrategy)) : Int :=
  let alice_strat := s PDPlayer.Alice
  let bob_strat := s PDPlayer.Bob
  match p, alice_strat, bob_strat with
  | PDPlayer.Alice, strat1, strat2 => match strat1, strat2 with
    | PDStrategy.Cooperate, PDStrategy.Cooperate => 1
    | PDStrategy.Cooperate, PDStrategy.Defect => -1
    | PDStrategy.Defect, PDStrategy.Cooperate => 2
    | PDStrategy.Defect, PDStrategy.Defect => 0
  | PDPlayer.Bob, strat1, strat2 => match strat1, strat2 with
    | PDStrategy.Cooperate, PDStrategy.Cooperate => 1
    | PDStrategy.Cooperate, PDStrategy.Defect => 2
    | PDStrategy.Defect, PDStrategy.Cooperate => -1
    | PDStrategy.Defect, PDStrategy.Defect => 0

def PDPreference (p : PDPlayer) : Preference (JointStrategy PDPlayer (fun _ => PDStrategy)) :=
  preference_from_utility (prisoner_utility p)

def PrisonersDilemma [DecidableEq PDPlayer] : Game where
  Player := PDPlayer
  Strategy := fun _ => PDStrategy
  JointPreference := PDPreference

--Results about the Prisoners' Dilemma

-- Define the mutual cooperation joint strategy where both players choose to cooperate
def mutual_cooperation : JointStrategy PDPlayer (fun _ => PDStrategy) :=
  fun _ => PDStrategy.Cooperate

--Work in progress

/-
-- Prove that mutual cooperation is not a Nash equilibrium
theorem mutual_cooperation_not_nash_equilibrium [DecidableEq PDPlayer] :
  ¬ is_nash_equilibrium PrisonersDilemma mutual_cooperation := by
  let s_new := unilateral_deviation PrisonersDilemma mutual_cooperation PDPlayer.Alice PDStrategy.Defect

  have h_utility_coop : prisoner_utility PDPlayer.Alice mutual_cooperation = 1,
  {
    unfold prisoner_utility,
    simp [mutual_cooperation],
  },

  have h_utility_defect : prisoner_utility PDPlayer.Alice s_new = 2,
  {
    unfold prisoner_utility,
    simp [s_new, unilateral_deviation, mutual_cooperation],
  },

  have h_prefer : prisoner_utility PDPlayer.Alice s_new > prisoner_utility PDPlayer.Alice mutual_cooperation,
  {
    rw [h_utility_defect, h_utility_coop],
    linarith,
  },

  have h_pref_relation : (PrisonersDilemma.JointPreference PDPlayer.Alice).le mutual_cooperation s_new = false,
  {
    unfold preference_from_utility,
    rw [h_utility_coop, h_utility_defect],
    simp,
  },

  unfold is_nash_equilibrium at *,
  intro h_nash,
  specialize h_nash PDPlayer.Alice PDStrategy.Defect,
  rw h_pref_relation at h_nash,
  contradiction,
-/

/-
-- Define the mutual defection joint strategy where both players choose to defect
def mutual_defection : JointStrategy PDPlayer (fun _ => PDStrategy) :=
  fun _ => PDStrategy.Defect

-- Prove that mutual defection is a Nash equilibrium
theorem mutual_defection_is_nash_equilibrium :
  is_nash_equilibrium PrisonersDilemma mutual_defection :=
begin
  intros p s',
  let s_new := unilateral_deviation PrisonersDilemma mutual_defection p s',

  -- Simplify by handling both cases directly without separate utility computations
  cases s'; cases p;
  -- Now all cases are concrete and can be computed directly
  all_goals {
    unfold PrisonersDilemma.JointPreference,
    unfold preference_from_utility,
    unfold prisoner_utility,
    simp [unilateral_deviation, mutual_defection],
    -- Use direct integer comparisons
    norm_num
  }
end
-/
