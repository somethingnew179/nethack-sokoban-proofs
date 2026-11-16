import Owner1007.Gate265Markers11
namespace Owner1007.SmallRestMarkers11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Owner1007.Gate265Markers11
theorem stationary_before {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (zeroRest : energy soko1_1.initial final UpperBudget11.Rest outcomes<2)
 (boundary : FirstCut Gate265Transport11.paid soko1_1.initial soko1_1.initial.boulders dirs final pushes moves outcomes)
 (cell : Cell) (member : cell∈([264,266] : List Cell)) :
 ownPushes [cell] boundary.beforeOutcomes=0 := by
 have cellRest : cell∈UpperBudget11.Rest := by
   simp only [List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl <;> decide
 rcases first_cut_or_quiet (paid:=firstPaid cell) boundary.before.logged [cell] with found|quiet
 ·obtain ⟨first⟩ := found
  have fixed := first.before.fixed (by simp :cell∈[cell]) (by intro dir;rfl)
  have tag : endGroup [cell] first.beforeOutcomes=[cell] := no_push_unchanged _ _ fixed
  obtain ⟨source,owner,metadata,same⟩ := first.headPaid
  change source=cell at same
  subst source
  have selected := first.before.logged.end_subset (by decide) [cell] (by simp) (by intro c h;have eq:=List.mem_singleton.mp h;subst c;exact (show UpperBudget11.Rest⊆soko1_1.initial.boulders from by decide) cellRest)
  have present : cell∈first.middle.boulders := selected.2 (by rw [tag];simp)
  have sourceMember : cell∈endGroup soko1_1.initial.boulders first.beforeOutcomes := by
    rw [HeroLedger.Logged.end_all first.before.logged]
    exact present
  have restSelected := first.before.logged.end_subset (by decide) UpperBudget11.Rest (by decide) (by decide)
  have singletonInRest : [cell]⊆UpperBudget11.Rest := by simpa using cellRest
  have included := end_subset_selected first.before.logged (by decide) [cell] UpperBudget11.Rest
    (by simp) (by decide) singletonInRest (by decide)
  have ownerRest : cell∈endGroup UpperBudget11.Rest first.beforeOutcomes := included (by rw [tag];simp)
  have countZero := FirstRest18711.quiet_count_zero boundary.before
  have forbidden (pays : Gate265Transport11.paid cell first.direction) : False := by
    have countPos := PaidCount11.event_le (paid:=Gate265Transport11.paid)
      (lastDirs:=first.afterDirs) (last:=first.afterOutcomes) first.before.logged first.headEffect
      soko1_1.initial.boulders ⟨cell,sourceMember,metadata,pays⟩
    rw [←first.dirsEq,←first.outcomesEq] at countPos
    omega
  have positive (pays : Triangle29111.paid cell first.direction) : False := by
    have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.before.logged.trace
    have row := Triangle29111.exit_row valid restSelected.1 restSelected.2 first.headChecked first.headEffect ownerRest metadata pays
    let last := first.after.append (Logged.cons boundary.headChecked boundary.headEffect boundary.after)
    have gap := logged_event_gap_le first.before.logged first.headChecked first.headEffect last UpperBudget11.Rest (by decide) (by decide)
    have allEffects : first.beforeOutcomes++first.headOutcome::(first.afterOutcomes++boundary.headOutcome::boundary.afterOutcomes)=outcomes := by
      calc
        _=(first.beforeOutcomes++first.headOutcome::first.afterOutcomes)++boundary.headOutcome::boundary.afterOutcomes := by simp only [List.append_assoc,List.cons_append]
        _=boundary.beforeOutcomes++boundary.headOutcome::boundary.afterOutcomes :=
          congrArg (fun before=>before++boundary.headOutcome::boundary.afterOutcomes) first.outcomesEq.symm
        _=outcomes := boundary.outcomesEq.symm
    have threshold : 2≤Triangle29111.threshold cell := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl <;> decide
    have bound := Int.le_trans threshold (Int.le_trans row gap)
    change 2≤energy soko1_1.initial final UpperBudget11.Rest
      (first.beforeOutcomes++first.headOutcome::(first.afterOutcomes++boundary.headOutcome::boundary.afterOutcomes)) at bound
    rw [allEffects] at bound
    omega
  have dirs := head_ew member present first.headChecked metadata
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl
  ·rcases dirs with east|west
   ·exact False.elim (forbidden (Or.inr (Or.inl ⟨rfl,east⟩)))
   ·exact False.elim (positive (Or.inl ⟨rfl,west⟩))
  ·rcases dirs with east|west
   ·exact False.elim (positive (Or.inr (Or.inl ⟨rfl,east⟩)))
   ·exact False.elim (forbidden (Or.inr (Or.inr (Or.inl ⟨rfl,west⟩))))
 ·exact quiet.fixed (by simp) (by intro dir;rfl)
#print axioms stationary_before
end Owner1007.SmallRestMarkers11
