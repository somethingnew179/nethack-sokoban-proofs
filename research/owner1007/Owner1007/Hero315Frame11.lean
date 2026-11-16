import NetHack.Soko11Hero315.Verified
import Owner1007.HeroLedgerPartitions
import Owner1007.BudgetWords11

namespace Owner1007.Hero315Frame11
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting

abbrev scalar := NetHack.Soko11Hero315.certificate NetHack.Soko11Hero315.all_walk_rows
  NetHack.Soko11Hero315.all_push_rows NetHack.Soko11Hero315.all_advance_rows

abbrev groupCertificate (limit : Nat) :=
  GhostPhaseCertificate.asOriginalCertificate (GhostScalar.asOracleCertificate scalar limit)

def weightAt (state : State) : Cell → Int :=
  NetHack.Soko11Hero315.weight
    (HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state) state.player
def value (state : State) (group : List Cell) : Int := weightSum (weightAt state) group
def energy (initial final : State) (group : List Cell) (outcomes : List Outcome) : Int :=
  HeroLedger.energy value NetHack.Soko11Hero315.holeWeight initial final group outcomes

theorem certificate_value (limit : Nat) (state : State) (group : List Cell) :
    (groupCertificate limit).groupValue state group = value state group := rfl

theorem before_fill (limit : Nat) (state : State) (group : List Cell)
    (holes : state.holes = soko1_1.initial.holes) :
    (groupCertificate limit).groupValue state group = BudgetWords11.value0 state group := by
  have phase : HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state = 0 := by
    simp [HazardPhaseCountedCorrection.phaseOf, holes]
  rw [certificate_value]
  simp only [value, weightAt, phase, BudgetWords11.value0, ZeroWord11.weight]

theorem goal_value_zero {final : State} (completed : Goal final) (group : List Cell) :
    value final group = 0 := by
  have phase : HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes final = 16 := by
    have empty : final.holes = [] := completed
    simp only [HazardPhaseCountedCorrection.phaseOf, empty, List.length_nil, Nat.sub_zero]
    rfl
  have zero (box : Cell) : weightAt final box = 0 := by
    change NetHack.Soko11Hero315.weight _ final.player box = 0
    rw [phase]
    exact NetHack.Soko11Hero315.terminal final.player box
  induction group with
  | nil => rfl
  | cons c rest ih => simpa only [value, weightSum, zero, Int.zero_add] using ih

theorem energy_nonnegative {dirs final pushes moves outcomes}
    (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
    (group : List Cell) (unique : group.Nodup) (inside : group ⊆ soko1_1.initial.boulders) :
    0 ≤ energy soko1_1.initial final group outcomes := by
  have size := List.Nodup.length_le_of_subset unique inside
  exact HeroLedger.Logged.energy_nonnegative logged (groupCertificate 18)
    NetHack.SokobanLinearPhases.Map11.initial_good group unique inside size

theorem total_energy {dirs final pushes moves outcomes}
    (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
    (completed : Goal final) :
    energy soko1_1.initial final soko1_1.initial.boulders outcomes = Int.ofNat pushes - 315 := by
  have total := HeroLedger.Logged.total_energy logged weightAt NetHack.Soko11Hero315.holeWeight
  have initial : weightSum (weightAt soko1_1.initial) soko1_1.initial.boulders +
      weightSum NetHack.Soko11Hero315.holeWeight soko1_1.initial.holes = 315 :=
    NetHack.Soko11Hero315.proposed_initial_value
  have zero := goal_value_zero completed final.boulders
  have empty : final.holes = [] := completed
  change weightSum (weightAt final) final.boulders = 0 at zero
  rw [initial, zero, empty] at total
  change energy soko1_1.initial final soko1_1.initial.boulders outcomes =
    Int.ofNat pushes + 0 + 0 - 315 at total
  simpa only [Int.add_zero] using total

theorem survivor_energy {dirs final pushes moves outcomes}
    (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
    (completed : Goal final) (cell : Cell) (survives : endGroup [cell] outcomes ≠ []) :
    energy soko1_1.initial final [cell] outcomes = Int.ofNat (ownPushes [cell] outcomes) -
      value soko1_1.initial [cell] :=
  HeroLedger.survivor_energy value NetHack.Soko11Hero315.holeWeight soko1_1.initial final cell
    outcomes survives (goal_value_zero completed _)

#print axioms NetHack.Soko11Hero315.pushes_lower_bound
#print axioms energy_nonnegative
#print axioms total_energy
#print axioms survivor_energy
end Owner1007.Hero315Frame11
