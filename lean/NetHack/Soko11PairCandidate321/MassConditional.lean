/- A stronger conditional reduction: rows are needed only where the raw
pair table exceeds the proved last-fill mass base. The final value is their
MAXIMUM, never the sum of two lower bounds. No new unconditional321 yet. -/
import NetHack.Soko11PairCandidate321.Conditional
import NetHack.Soko11Sparse319.Value
import NetHack.Sokoban.GhostLastFillOracle
import NetHack.Sokoban.GhostPhaseCorrection
namespace NetHack.Soko11PairCandidate321
open NetHack.Sokoban NetHack.Sokoban.GhostPartition NetHack.Sokoban.HazardPattern
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem scalar_nonpositive (phase hero box : Nat) : scalar.weight phase hero box ≤ 0 :=
  NetHack.Soko11Sparse319.weight_nonpositive phase hero box
theorem scalar_terminal_zero (hero box : Nat) : scalar.weight soko1_1.initial.holes.length hero box = 0 :=
  NetHack.Soko11Hero315.terminal hero box
def massBasis := GhostLastFillOracle.asOracleCertificate scalar scalar_nonpositive scalar_terminal_zero
def excess (phase hero : Nat) (group : List Cell) : Nat :=
  (valueAt phase hero group - massBasis.valueAt phase hero group).toNat
def combined (phase hero : Nat) (group : List Cell) : Int :=
  GhostPhaseCorrection.corrected massBasis excess phase hero group

theorem combined_eq_max (phase hero : Nat) (group : List Cell) :
    combined phase hero group = max (massBasis.valueAt phase hero group) (valueAt phase hero group) := by
  unfold combined GhostPhaseCorrection.corrected excess
  simp only [Int.ofNat_eq_natCast,Int.ofNat_toNat,Int.max_def]
  split <;> split <;> omega

theorem raw_le_combined (phase hero : Nat) (group : List Cell) : valueAt phase hero group ≤ combined phase hero group := by
  rw [combined_eq_max]
  exact Int.le_max_right _ _

def AllExcessActions : Prop :=
  ∀ phase, phase < 16 → ∀ hero ∈ NetHack.Soko11Hero315.phases.heroes phase,
    ∀ group, group.Nodup → group ⊆ NetHack.Soko11Hero315.phases.crates phase → group.length ≤ 2 →
    hero ∈ soko1_1.board.floor → hero ∉ soko1_1.board.doors →
    hero ∉ soko1_1.initial.holes.drop phase → hero ∉ group →
    massBasis.valueAt phase hero group < valueAt phase hero group → ∀ direction outcome,
    stepOracle soko1_1.board (PatternCorrection.project group)
      (PatternCorrection.project (soko1_1.initial.holes.drop phase)) hero direction = some outcome →
    localBound phase hero group outcome
def AllExcessEnvironments : Prop :=
  ∀ phase, phase < 16 → ∀ hero ∈ NetHack.Soko11Hero315.phases.heroes phase,
    ∀ group, group.Nodup → group ⊆ NetHack.Soko11Hero315.phases.crates phase →
    group ⊆ NetHack.Soko11Hero315.phases.crates (phase+1) → group.length ≤ 2 →
    hero ∈ soko1_1.board.floor → hero ∉ soko1_1.board.doors →
    hero ∉ soko1_1.initial.holes.drop phase → hero ∉ group →
    massBasis.valueAt phase hero group < valueAt phase hero group →
    valueAt phase hero group ≤ valueAt (phase+1) hero group

theorem raw_terminal_zero (hero : Nat) (group : List Cell) : valueAt 16 hero group = 0 := by
  have sum (cells : List Cell) : LowerBounds.weightSum (NetHack.Soko11Hero315.weight 16 hero) cells = 0 := by
    induction cells with
    | nil => rfl
    | cons first rest ih =>
      have head : NetHack.Soko11Hero315.weight 16 hero first = 0 := NetHack.Soko11Hero315.terminal hero first
      rw [LowerBounds.weightSum_cons,head,ih]; rfl
  have bit : bonus 16 hero group = 0 := by simp [bonus,tables,lookup]
  unfold valueAt
  rw [bit,sum group]
  rfl

def massCorrection (actions : AllExcessActions) (environments : AllExcessEnvironments) :
    GhostPhaseCorrection.Correction massBasis where
  bonus := excess
  positive_row := by
    intro phase active hero heroInside group unique inside length floor door hole clear positive direction outcome oracle
    have greater : massBasis.valueAt phase hero group < valueAt phase hero group := by
      change 0 < (valueAt phase hero group - massBasis.valueAt phase hero group).toNat at positive
      omega
    have beforeEq : combined phase hero group = valueAt phase hero group := by
      rw [combined_eq_max,Int.max_eq_right (by omega)]
    have numeric := actions phase active hero heroInside group unique inside length floor door hole clear greater direction outcome oracle
    have after := raw_le_combined (HazardPhaseCountedCorrection.nextPhase phase outcome) (nextHero outcome) (update group outcome)
    change combined phase hero group ≤ charge NetHack.Soko11Hero315.holeWeight group outcome +
      combined (HazardPhaseCountedCorrection.nextPhase phase outcome) (nextHero outcome) (update group outcome)
    rw [beforeEq]
    unfold localBound at numeric
    omega
  positive_environment := by
    intro phase active hero heroInside group unique inside nextInside length floor door hole clear positive
    have greater : massBasis.valueAt phase hero group < valueAt phase hero group := by
      change 0 < (valueAt phase hero group - massBasis.valueAt phase hero group).toNat at positive
      omega
    have beforeEq : combined phase hero group = valueAt phase hero group := by rw [combined_eq_max,Int.max_eq_right (by omega)]
    have numeric := environments phase active hero heroInside group unique inside nextInside length floor door hole clear greater
    have after := raw_le_combined (phase+1) hero group
    change combined phase hero group ≤ combined (phase+1) hero group
    rw [beforeEq]
    omega
  terminal_bonus := by
    intro hero group
    change excess 16 hero group = 0
    change (valueAt 16 hero group - GhostLastFillOracle.valueAt scalar 16 hero group).toNat = 0
    have last : GhostLastFillOracle.valueAt scalar 16 hero group = 0 :=
      GhostLastFillOracle.terminal_zero scalar scalar_terminal_zero hero group
    rw [raw_terminal_zero,last]
    rfl

theorem combined_initial_eq (hero : Nat) (group : List Cell) :
    combined 0 hero group = valueAt 0 hero group := by
  rw [combined_eq_max]
  have before : massBasis.valueAt 0 hero group = LowerBounds.weightSum (scalar.weight 0 hero) group := rfl
  rw [before]
  apply Int.max_eq_right
  change LowerBounds.weightSum (scalar.weight 0 hero) group ≤
    LowerBounds.weightSum (scalar.weight 0 hero) group + Int.ofNat (bonus 0 hero group)
  simp only [Int.ofNat_eq_natCast]
  omega

/-- Still CONDITIONAL on all phases' excess rows. The proved mass bound
justifies omitting other rows; it is not an extra original Trace premise. -/
theorem lower321_of_all_excess_rows (actions : AllExcessActions) (environments : AllExcessEnvironments)
    {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko1_1.board soko1_1.initial directions final pushes moves) (completed : Goal final) :
    321 ≤ pushes := by
  let cert := GhostPhaseCorrection.asOriginalCertificate (massCorrection actions environments)
  have initial : partitionValue cert soko1_1.initial initialGroups = Int.ofNat 321 := by
    change sumGroups (combined 0 soko1_1.initial.player) initialGroups +
      LowerBounds.weightSum NetHack.Soko11Hero315.holeWeight soko1_1.initial.holes = 321
    have eq : combined 0 soko1_1.initial.player = valueAt 0 soko1_1.initial.player :=
      funext fun group => combined_initial_eq _ group
    rw [eq]
    exact candidate_initial_value
  exact partition_pushes_lower_bound cert soko1_1.initial initialGroups
    NetHack.SokobanLinearPhases.Map11.initial_good initial_coupled initial_capacity 321 initial trace completed

end NetHack.Soko11PairCandidate321
