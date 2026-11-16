import Owner1007.HeroLedger

namespace Owner1007.HeroLedger
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition Owner1007.TokenAccounting

theorem holeOnly_debt (credits : Cell → Int) (group : List Cell) :
    Owner1007.debtOf (holeOnly credits) group = 0 := by
  induction group with
  | nil => rfl
  | cons c rest ih => simpa [Owner1007.debtOf, holeOnly, weightSum] using ih

theorem charges_eq_potential_energy (credits : Cell → Int) (group : List Cell) (outcomes : List Outcome) :
    charges credits group outcomes = TokenAccounting.energy (holeOnly credits) group outcomes := by
  have ledger := group_ledger (holeOnly credits) group outcomes
  have account := charges_eq_own credits group outcomes
  rw [holeOnly_debt, holeOnly_debt] at ledger
  unfold TokenAccounting.energy
  rw [holeOnly_debt]
  omega

theorem Logged.charges_split {board initial dirs final pushes moves outcomes}
    (logged : Logged board initial dirs final pushes moves outcomes)
    (actualUnique : initial.boulders.Nodup) (credits : Cell → Int) (first second : List Cell)
    (unique : (first ++ second).Nodup) (inside : first ++ second ⊆ initial.boulders) :
    charges credits (first ++ second) outcomes = charges credits first outcomes + charges credits second outcomes := by
  simpa only [charges_eq_potential_energy] using
    TokenAccounting.Logged.energy_split logged actualUnique (holeOnly credits) first second unique inside

theorem Logged.end_append_perm {board initial dirs final pushes moves outcomes}
    (logged : Logged board initial dirs final pushes moves outcomes)
    (actualUnique : initial.boulders.Nodup) (first second : List Cell)
    (unique : (first ++ second).Nodup) (inside : first ++ second ⊆ initial.boulders) :
    (endGroup (first ++ second) outcomes).Perm
      (endGroup first outcomes ++ endGroup second outcomes) := by
  induction logged generalizing first second with
  | nil => exact List.Perm.refl _
  | @cons state dir t rest final pushes moves outcome outcomes head effect tail ih =>
    have nextActual := step_boulders_nodup _ _ _ _ actualUnique head
    have bothUnique := GhostSubset.update_unique _ _ _ effect nextActual (first++second) unique inside
    have bothInside := GhostSubset.update_subset _ _ _ effect (first++second) unique inside
    have pair := GhostSubset.pair_update_perm first second unique outcome
    have nextUnique := pair.nodup_iff.mpr bothUnique
    have nextInside : update first outcome ++ update second outcome ⊆ t.state.boulders :=
      fun _ h => bothInside (pair.mem_iff.mp h)
    have later := ih nextActual (update first outcome) (update second outcome) nextUnique nextInside
    exact (endGroup_perm pair.symm outcomes).trans later

def scalarValue (weight : State → Cell → Int) (state : State) (group : List Cell) : Int :=
  weightSum (weight state) group

/-- Exact additivity includes each group's own hero and phase dependent value. -/
theorem Logged.energy_split {board initial dirs final pushes moves outcomes}
    (logged : Logged board initial dirs final pushes moves outcomes)
    (actualUnique : initial.boulders.Nodup) (weight : State → Cell → Int) (credits : Cell → Int)
    (first second : List Cell) (unique : (first ++ second).Nodup)
    (inside : first ++ second ⊆ initial.boulders) :
    energy (scalarValue weight) credits initial final (first ++ second) outcomes =
      energy (scalarValue weight) credits initial final first outcomes +
      energy (scalarValue weight) credits initial final second outcomes := by
  have charged := Logged.charges_split logged actualUnique credits first second unique inside
  have perm := Logged.end_append_perm logged actualUnique first second unique inside
  have terminal := StatePermutation.weightSum_permutation (weight final) perm
  rw [GhostScalar.weightSum_append] at terminal
  unfold energy scalarValue
  rw [charged, terminal, GhostScalar.weightSum_append]
  omega

theorem Logged.end_all {board initial dirs final pushes moves outcomes}
    (logged : Logged board initial dirs final pushes moves outcomes) :
    endGroup initial.boulders outcomes = final.boulders := by
  induction logged with
  | nil => rfl
  | cons head effect tail ih =>
    simpa only [endGroup, (matches_full_update _ _ _ effect).1] using ih

/-- The sum of all group energies is the original full-map slack budget. -/
theorem Logged.total_energy {board initial dirs final pushes moves outcomes}
    (logged : Logged board initial dirs final pushes moves outcomes)
    (weight : State → Cell → Int) (credits : Cell → Int) :
    energy (scalarValue weight) credits initial final initial.boulders outcomes =
      Int.ofNat pushes + weightSum (weight final) final.boulders + weightSum credits final.holes -
        (weightSum (weight initial) initial.boulders + weightSum credits initial.holes) := by
  have total := logged.all_energy (holeOnly credits)
  rw [←charges_eq_potential_energy] at total
  have value : (holeOnly credits).value initial = weightSum credits initial.holes := by
    simp only [Potential.value, holeOnly]
    have zero : weightSum (fun _ => (0 : Int)) initial.boulders = 0 := by
      induction initial.boulders with
      | nil => rfl
      | cons c rest ih => simpa only [weightSum, Int.zero_add] using ih
    rw [zero, Int.zero_add]
  rw [value] at total
  unfold energy scalarValue
  rw [Logged.end_all logged]
  change weightSum credits initial.holes + charges credits initial.boulders outcomes =
    Int.ofNat pushes + weightSum credits final.holes at total
  omega

#print axioms Logged.energy_split
#print axioms Logged.total_energy
end Owner1007.HeroLedger
