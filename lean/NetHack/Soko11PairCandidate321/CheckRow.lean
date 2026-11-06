/- Executable obligations for persistent pairs, not a push-graph reduction.
Every original direction is enumerated using the existing endpoint oracle.
The additional environment-advance inequality covers OTHER boulders' fills.
Checking a few literal pairs does not cover all future positions of a group. -/
import NetHack.Soko11PairCandidate321.Data
namespace NetHack.Soko11PairCandidate321
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def valueAt (phase hero : Nat) (group : List Cell) : Int :=
  weightSum (NetHack.Soko11Hero315.weight phase hero) group + Int.ofNat (bonus phase hero group)

def localBound (phase hero : Nat) (group : List Cell) (outcome : Outcome) : Prop :=
  valueAt phase hero group ≤
    charge NetHack.Soko11Hero315.holeWeight group outcome +
      valueAt (HazardPhaseCountedCorrection.nextPhase phase outcome) (nextHero outcome) (update group outcome)
instance (phase hero : Nat) (group : List Cell) (outcome : Outcome) :
    Decidable (localBound phase hero group outcome) := by unfold localBound; infer_instance

def actionCheck (phase hero : Nat) (group : List Cell) : Bool :=
  allDirs.all fun direction =>
    match stepOracle soko1_1.board (PatternCorrection.project group)
      (PatternCorrection.project (soko1_1.initial.holes.drop phase)) hero direction with
    | none => true
    | some outcome => decide (localBound phase hero group outcome)

def environmentCheck (phase hero : Nat) (group : List Cell) : Bool :=
  if hero ∉ group ∧ phase < 16 then
    decide (valueAt phase hero group ≤ valueAt (phase+1) hero group)
  else true

def rowCheck (phase : Nat) (group : List Cell) : Bool :=
  (NetHack.Soko11Hero315.phases.heroes phase).all fun hero =>
    actionCheck phase hero group && environmentCheck phase hero group

theorem rowCheck_actions (phase : Nat) (group : List Cell) (checked : rowCheck phase group = true)
    (hero : Cell) (member : hero ∈ NetHack.Soko11Hero315.phases.heroes phase)
    (direction : Dir) (outcome : Outcome)
    (oracle : stepOracle soko1_1.board (PatternCorrection.project group)
      (PatternCorrection.project (soko1_1.initial.holes.drop phase)) hero direction = some outcome) :
    localBound phase hero group outcome := by
  have pair := Bool.and_eq_true_iff.mp (List.all_eq_true.mp checked hero member)
  have numeric := List.all_eq_true.mp pair.1 direction (Geometry.all_directions direction)
  rw [oracle] at numeric
  exact of_decide_eq_true numeric

theorem rowCheck_environment (phase : Nat) (group : List Cell) (checked : rowCheck phase group = true)
    (hero : Cell) (member : hero ∈ NetHack.Soko11Hero315.phases.heroes phase)
    (clear : hero ∉ group) (active : phase < 16) :
    valueAt phase hero group ≤ valueAt (phase+1) hero group := by
  have pair := Bool.and_eq_true_iff.mp (List.all_eq_true.mp checked hero member)
  have numeric := pair.2
  simp only [environmentCheck,if_pos (And.intro clear active)] at numeric
  exact of_decide_eq_true numeric

end NetHack.Soko11PairCandidate321
