/- EXACT proof boundary: lower321 remains conditional on all positive
pair rows in all16 original phases. The literal initial value and two pilot
rows cannot discharge these universal fields. Current InitialIntervals stays319. -/
import NetHack.Soko11PairCandidate321.CheckRow
import NetHack.Sokoban.GhostNonlinear
import NetHack.Sokoban.GhostPartitionPermutation
namespace NetHack.Soko11PairCandidate321
open NetHack.Sokoban NetHack.Sokoban.GhostPartition NetHack.Sokoban.HazardPattern
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def scalar := NetHack.Soko11Hero315.certificate NetHack.Soko11Hero315.all_walk_rows
  NetHack.Soko11Hero315.all_push_rows NetHack.Soko11Hero315.all_advance_rows

def AllPositiveActions : Prop :=
  ∀ phase, phase < 16 → ∀ hero ∈ NetHack.Soko11Hero315.phases.heroes phase,
    ∀ group, group.Nodup → group ⊆ NetHack.Soko11Hero315.phases.crates phase → group.length ≤ 2 →
    hero ∈ soko1_1.board.floor → hero ∉ soko1_1.board.doors →
    hero ∉ soko1_1.initial.holes.drop phase → hero ∉ group → 0 < bonus phase hero group →
    ∀ direction outcome,
    stepOracle soko1_1.board (PatternCorrection.project group)
      (PatternCorrection.project (soko1_1.initial.holes.drop phase)) hero direction = some outcome →
    localBound phase hero group outcome

def AllPositiveEnvironments : Prop :=
  ∀ phase, phase < 16 → ∀ hero ∈ NetHack.Soko11Hero315.phases.heroes phase,
    ∀ group, group.Nodup → group ⊆ NetHack.Soko11Hero315.phases.crates phase →
    group ⊆ NetHack.Soko11Hero315.phases.crates (phase+1) → group.length ≤ 2 →
    hero ∈ soko1_1.board.floor → hero ∉ soko1_1.board.doors →
    hero ∉ soko1_1.initial.holes.drop phase → hero ∉ group → 0 < bonus phase hero group →
    valueAt phase hero group ≤ valueAt (phase+1) hero group

def correction_of_all_positive (actions : AllPositiveActions) (environments : AllPositiveEnvironments) :
    GhostNonlinear.Correction scalar 2 where
  bonus := bonus
  positive_row := actions
  positive_environment := environments
  terminal_bonus := by
    intro hero group
    change bonus 16 hero group = 0
    simp [bonus,tables,lookup]

theorem valueAt_respects (phase hero : Nat) (a b : List Cell) (related : a.Perm b) :
    valueAt phase hero a = valueAt phase hero b := by
  have main := StatePermutation.weightSum_permutation (NetHack.Soko11Hero315.weight phase hero) related
  have index := StatePermutation.weightSum_permutation codeWeight related
  simp only [valueAt,bonus,code,main,index,related.length_eq]

theorem localBound_respects (phase hero : Nat) (a b : List Cell) (related : a.Perm b) (outcome : Outcome) :
    localBound phase hero a outcome ↔ localBound phase hero b outcome := by
  unfold localBound
  rw [valueAt_respects phase hero a b related,charge_permutation _ a b related outcome,
    valueAt_respects _ _ _ _ (update_permutation a b related outcome)]

/-- CONDITIONAL, not the registered universal lower bound. All16-phase
positive action/environment fields still must be supplied as checked proofs. -/
theorem lower321_of_all_positive_rows (actions : AllPositiveActions) (environments : AllPositiveEnvironments)
    {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko1_1.board soko1_1.initial directions final pushes moves) (completed : Goal final) :
    321 ≤ pushes := by
  let cert := GhostNonlinear.asOriginalCertificate (correction_of_all_positive actions environments)
  have initial : partitionValue cert soko1_1.initial initialGroups = Int.ofNat 321 := by
    change candidateValue soko1_1.initial initialGroups = 321
    exact candidate_initial_value
  exact partition_pushes_lower_bound cert soko1_1.initial initialGroups
    NetHack.SokobanLinearPhases.Map11.initial_good initial_coupled initial_capacity
    321 initial trace completed

end NetHack.Soko11PairCandidate321
