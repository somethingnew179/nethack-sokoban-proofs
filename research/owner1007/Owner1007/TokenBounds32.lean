import Owner1007.LeftEnergy32

namespace Owner1007.TokenAccounting
open NetHack.Sokoban NetHack.Sokoban.LowerBounds
open NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition

theorem Logged.end_split {board initial dirs final pushes moves outcomes}
    (logged : Logged board initial dirs final pushes moves outcomes)
    (actualUnique : initial.boulders.Nodup) (first second : List Cell)
    (unique : (first ++ second).Nodup) (subset : first ++ second ⊆ initial.boulders) :
    (endGroup first outcomes ++ endGroup second outcomes).Perm (endGroup (first ++ second) outcomes) := by
  induction logged generalizing first second with
  | nil => exact .refl _
  | @cons state dir t rest final pushes moves outcome outcomes head effect tail ih =>
    have nextActual := step_boulders_nodup _ _ _ _ actualUnique head
    have bothUnique := GhostSubset.update_unique _ _ _ effect nextActual (first++second) unique subset
    have bothSubset := GhostSubset.update_subset _ _ _ effect (first++second) unique subset
    have pair := GhostSubset.pair_update_perm first second unique outcome
    have nextUnique := pair.nodup_iff.mpr bothUnique
    have nextSubset : update first outcome ++ update second outcome ⊆ t.state.boulders :=
      fun _ h => bothSubset (pair.mem_iff.mp h)
    have middle := ih nextActual (update first outcome) (update second outcome) nextUnique nextSubset
    exact middle.trans (endGroup_perm pair outcomes)

theorem Logged.member_energy_le {board initial dirs final pushes moves outcomes}
    (logged : Logged board initial dirs final pushes moves outcomes)
    {potential : Potential} (valid : Valid board potential)
    (actualUnique : initial.boulders.Nodup) (group : List Cell) (unique : group.Nodup)
    (subset : group ⊆ initial.boulders) (cell : Cell) (member : cell ∈ group) :
    energy potential [cell] outcomes ≤ energy potential group outcomes := by
  have same := (List.perm_cons_erase member).symm
  have splitUnique : ([cell] ++ group.erase cell).Nodup := same.nodup_iff.mpr unique
  have splitSubset : [cell] ++ group.erase cell ⊆ initial.boulders :=
    fun _ h => subset (same.mem_iff.mp h)
  have split := logged.energy_split actualUnique potential [cell] (group.erase cell) splitUnique splitSubset
  have perm := energy_perm potential same outcomes
  have combined := split.symm.trans perm
  have nonnegative := logged.energy_nonnegative valid (group.erase cell)
  omega

theorem singleton_end_shape (cell : Cell) (outcomes : List Outcome) :
    endGroup [cell] outcomes = [] ∨ ∃ last, endGroup [cell] outcomes = [last] := by
  have count := endGroup_length_le [cell] outcomes
  cases shape : endGroup [cell] outcomes with
  | nil => exact Or.inl rfl
  | cons first rest =>
    apply Or.inr
    have empty : rest = [] := by
      have lengthZero : rest.length = 0 := by simp only [shape, List.length_cons, List.length_nil] at count; omega
      exact List.eq_nil_of_length_eq_zero lengthZero
    exact ⟨first, by rw [empty]⟩

end Owner1007.TokenAccounting

namespace Owner1007.EnergyFrame32
open NetHack.Sokoban NetHack.Sokoban.LowerBounds Owner1007.TokenAccounting

/-- The complete equality case below141. In particular139's terminal debt
is still allowed; only A and B have zero terminal debt. -/
theorem tight_budget {dirs final pushes moves outcomes}
    (logged : Logged soko3_2.board soko3_2.initial dirs final pushes moves outcomes)
    (completed : Goal final) (small : pushes ≤ 140) :
    energy potential32 G outcomes = 5 ∧ ownSlack potential32 A outcomes = 1 ∧
    ownSlack potential32 B outcomes = 0 ∧ debtOf potential32 (endGroup A outcomes) = 0 ∧
    debtOf potential32 (endGroup B outcomes) = 0 := by
  have total := energy_total logged completed
  have reserved := group_energy_five logged completed
  have left := LeftPhases32.left_must_pay logged completed small
  have other := logged.ownSlack_nonnegative Generated.soko3_2_potential_valid B
  change 0 ≤ ownSlack potential32 B outcomes at other
  have nonnegative : ∀ cells, 0 ≤ debtOf potential32 cells := by
    intro cells
    exact NonlinearFacts.weightSum_nonnegative (fun c => -potential32.boulder c) cells
      (fun c => by have h := Generated.soko3_2_potential_valid.nonpositive c; change potential32.boulder c ≤ 0 at h; omega)
  have debtA := nonnegative (endGroup A outcomes)
  have debtB := nonnegative (endGroup B outcomes)
  change energy potential32 G outcomes +
    (ownSlack potential32 A outcomes + debtOf potential32 (endGroup A outcomes)) +
    (ownSlack potential32 B outcomes + debtOf potential32 (endGroup B outcomes)) = Int.ofNat pushes - 134 at total
  simp only [Int.ofNat_eq_natCast] at total
  omega

#print axioms tight_budget
end Owner1007.EnergyFrame32
