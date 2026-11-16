import Owner1007.GateSurvival32
import Owner1007.TokenCounting

namespace Owner1007.Lower141
open NetHack.Sokoban NetHack.Sokoban.LowerBounds
open Owner1007.TokenAccounting Owner1007.EnergyFrame32 Owner1007.GateSurvival32

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem positive_A_consumed {dirs final pushes moves outcomes}
    (logged : Logged soko3_2.board soko3_2.initial dirs final pushes moves outcomes)
    (completed : Goal final) (small : pushes ≤ 140) (cell : Cell) (member : cell ∈ A)
    (not80 : cell ≠ 80) (not132 : cell ≠ 132) : endGroup [cell] outcomes = [] := by
  have tight := tight_budget logged completed small
  have aEnergy : energy potential32 A outcomes = 1 := by
    unfold energy
    rw [tight.2.1, tight.2.2.2.1]
    rfl
  have bound := logged.member_energy_le Generated.soko3_2_potential_valid
    (by decide +kernel) A (by decide +kernel) (by decide +kernel) cell member
  change energy potential32 [cell] outcomes ≤ energy potential32 A outcomes at bound
  rw [aEnergy] at bound
  have positive : 0 < -potential32.boulder cell := by
    have finite : ∀ c ∈ A, c ≠ 80 → c ≠ 132 → 0 < -potential32.boulder c := by decide +kernel
    exact finite cell member not80 not132
  apply Classical.byContradiction
  intro survives
  have price := survivor_energy potential32 cell outcomes survives
  have noPush : ownPushes [cell] outcomes = 0 := by
    simp only [Int.ofNat_eq_natCast] at price
    omega
  have fixed := no_push_unchanged [cell] outcomes noPush
  have included := logged.member_debt_le Generated.soko3_2_potential_valid
    (by decide +kernel) A (by decide +kernel) (by decide +kernel) cell member
  change debtOf potential32 (endGroup [cell] outcomes) ≤ debtOf potential32 (endGroup A outcomes) at included
  rw [fixed, tight.2.2.2.1] at included
  simp only [debtOf, weightSum, Int.add_zero] at included
  omega

theorem too_few_survivors {dirs final pushes moves outcomes}
    (logged : Logged soko3_2.board soko3_2.initial dirs final pushes moves outcomes)
    (completed : Goal final) (small : pushes ≤ 140) : False := by
  have actualUnique : soko3_2.initial.boulders.Nodup := by decide +kernel
  have allSubset : G ++ (A ++ B) ⊆ soko3_2.initial.boulders :=
    fun _ h => initial_partition.mem_iff.mp h
  have aSubset : A ⊆ soko3_2.initial.boulders := by decide +kernel
  have bSubset : B ⊆ soko3_2.initial.boulders := by decide +kernel
  have gDead : ∀ cell ∈ G, ([139] : List Cell).contains cell = false → endGroup [cell] outcomes = [] := by
    intro cell member absent
    have different : cell ≠ 139 := by intro same; subst cell; simp at absent
    exact (heavy_energy_even logged completed small cell member different).1
  have aDead : ∀ cell ∈ A, ([80,132] : List Cell).contains cell = false → endGroup [cell] outcomes = [] := by
    intro cell member absent
    have not80 : cell ≠ 80 := by intro same; subst cell; simp at absent
    have not132 : cell ≠ 132 := by intro same; subst cell; simp at absent
    exact positive_A_consumed logged completed small cell member not80 not132
  have bDead : ∀ cell ∈ B, (fun _ : Cell => false) cell = false → endGroup [cell] outcomes = [] :=
    fun cell member _ => B_tokens_consumed logged completed small cell member
  have gCount := logged.end_count_le actualUnique G (List.nodup_append.mp initial_unique).1 g_subset
    ([139] : List Cell).contains gDead
  have aCount := logged.end_count_le actualUnique A (by decide +kernel) aSubset
    ([80,132] : List Cell).contains aDead
  have bCount := logged.end_count_le actualUnique B (by decide +kernel) bSubset
    (fun _ => false) bDead
  have gFilter : (G.filter ([139] : List Cell).contains).length = 1 := by decide +kernel
  have aFilter : (A.filter ([80,132] : List Cell).contains).length = 2 := by decide +kernel
  have bFilter : (B.filter (fun _ => false)).length = 0 := by decide +kernel
  rw [gFilter] at gCount
  rw [aFilter] at aCount
  rw [bFilter] at bCount
  have first := logged.end_split actualUnique G (A++B) initial_unique allSubset
  have second := logged.end_split actualUnique A B (List.nodup_append.mp initial_unique).2.1
    (fun _ h => allSubset (List.mem_append_right _ h))
  have firstLength := first.length_eq
  have secondLength := second.length_eq
  simp only [List.length_append] at firstLength secondLength
  have represented := (endGroup_perm initial_partition outcomes).length_eq
  rw [logged.all_end] at represented
  have conserved := logged.trace.conservation
  have empty : final.holes = [] := completed
  change 16 + final.holes.length = final.boulders.length + 12 at conserved
  rw [empty] at conserved
  simp only [List.length_nil] at conserved
  omega

/-- Universal lower bound from the ORIGINAL canonical full map and Model.
The proof uses compact occupancy phases, exact owned-energy accounting,
static parity, and the unavoidable count of four surviving identities. -/
theorem pushes_lower_bound {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko3_2.board soko3_2.initial directions final pushes moves)
    (completed : Goal final) : 141 ≤ pushes := by
  by_cases large : 141 ≤ pushes
  · exact large
  · have small : pushes ≤ 140 := by omega
    obtain ⟨outcomes, logged⟩ := log_exists trace (by decide +kernel)
    exact False.elim (too_few_survivors logged completed small)

#check @pushes_lower_bound
#print axioms pushes_lower_bound
end Owner1007.Lower141
