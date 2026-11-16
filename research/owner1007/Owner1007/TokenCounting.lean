import Owner1007.TokenBounds32

namespace Owner1007.TokenAccounting
open NetHack.Sokoban NetHack.Sokoban.LowerBounds
open NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition

theorem Logged.all_end {board initial dirs final pushes moves outcomes}
    (logged : Logged board initial dirs final pushes moves outcomes) :
    endGroup initial.boulders outcomes = final.boulders := by
  induction logged with
  | nil => rfl
  | cons head effect tail ih =>
    change endGroup (update _ _) _ = _
    rw [(matches_full_update _ _ _ effect).1]
    exact ih

theorem Logged.member_end_subset {board initial dirs final pushes moves outcomes}
    (logged : Logged board initial dirs final pushes moves outcomes)
    (actualUnique : initial.boulders.Nodup) (group : List Cell) (unique : group.Nodup)
    (subset : group ⊆ initial.boulders) (cell : Cell) (member : cell ∈ group) :
    endGroup [cell] outcomes ⊆ endGroup group outcomes := by
  have same := (List.perm_cons_erase member).symm
  have splitUnique : ([cell] ++ group.erase cell).Nodup := same.nodup_iff.mpr unique
  have splitSubset : [cell] ++ group.erase cell ⊆ initial.boulders :=
    fun _ h => subset (same.mem_iff.mp h)
  have split := logged.end_split actualUnique [cell] (group.erase cell) splitUnique splitSubset
  have perm := split.trans (endGroup_perm same outcomes)
  exact fun _ h => perm.mem_iff.mp (List.mem_append_left _ h)

theorem Logged.member_debt_le {board initial dirs final pushes moves outcomes}
    (logged : Logged board initial dirs final pushes moves outcomes)
    {potential : Potential} (valid : Valid board potential)
    (actualUnique : initial.boulders.Nodup) (group : List Cell) (unique : group.Nodup)
    (subset : group ⊆ initial.boulders) (cell : Cell) (member : cell ∈ group) :
    debtOf potential (endGroup [cell] outcomes) ≤ debtOf potential (endGroup group outcomes) := by
  have included := logged.member_end_subset actualUnique group unique subset cell member
  have singletonSubset : [cell] ⊆ initial.boulders := by
    intro c h
    have same : c = cell := by simpa using h
    subst c
    exact subset member
  have endUnique := (logged.end_subset actualUnique [cell] (by simp) singletonSubset).1
  exact NonlinearFacts.weightSum_le_of_nodup_subset (fun c => -potential.boulder c)
    (endGroup [cell] outcomes) (endGroup group outcomes)
    (fun c => by have h := valid.nonpositive c; omega) endUnique included

/-- A persistent original group has at most one survivor per permitted
initial identity. This counts identities, not just occupied cells. -/
theorem Logged.end_count_le {board initial dirs final pushes moves outcomes}
    (logged : Logged board initial dirs final pushes moves outcomes)
    (actualUnique : initial.boulders.Nodup) (group : List Cell) (unique : group.Nodup)
    (subset : group ⊆ initial.boulders) (allowed : Cell → Bool)
    (dead : ∀ cell ∈ group, allowed cell = false → endGroup [cell] outcomes = []) :
    (endGroup group outcomes).length ≤ (group.filter allowed).length := by
  induction group with
  | nil => simp [endGroup_empty]
  | cons cell rest ih =>
    have tailUnique := (List.nodup_cons.mp unique).2
    have tailSubset : rest ⊆ initial.boulders := fun c h => subset (List.mem_cons_of_mem _ h)
    have tailDead : ∀ c ∈ rest, allowed c = false → endGroup [c] outcomes = [] :=
      fun c h => dead c (List.mem_cons_of_mem _ h)
    have restBound := ih tailUnique tailSubset tailDead
    have split := logged.end_split actualUnique [cell] rest unique subset
    have count := split.length_eq
    simp only [List.length_append] at count
    change (endGroup [cell] outcomes).length + (endGroup rest outcomes).length =
      (endGroup (cell::rest) outcomes).length at count
    have single := endGroup_length_le [cell] outcomes
    simp only [List.length_cons, List.length_nil] at single
    cases chosen : allowed cell with
    | false =>
      have gone := dead cell (by simp) chosen
      rw [gone] at count
      simp only [List.length_nil, Nat.zero_add] at count
      simpa only [List.filter_cons, chosen, Bool.false_eq_true, ↓reduceIte] using
        (show (endGroup (cell::rest) outcomes).length ≤ (rest.filter allowed).length by omega)
    | true =>
      have bound : (endGroup (cell::rest) outcomes).length ≤ (rest.filter allowed).length + 1 := by omega
      simpa only [List.filter_cons, chosen, ↓reduceIte, List.length_cons] using bound

#print axioms Logged.end_count_le
end Owner1007.TokenAccounting
