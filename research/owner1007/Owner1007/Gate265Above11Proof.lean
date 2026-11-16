import Owner1007.Gate265Above11Geometry
import Owner1007.Triangle29111Prices
import Owner1007.Deep29133511
import Owner1007.LoggedEventGap11
import Owner1007.WestRankHead11
import Owner1007.QuietFixed11
import Owner1007.HeroEndSubset11
namespace Owner1007.Gate265Above11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def shapeCheck (i : Fin 2) (source : Cell) (dir : Dir) : Bool :=
 if paid source dir then match advance soko1_1.board source dir.opposite with
 |none=>true
 |some hero=>decide (hero∉region i ∨BlockedPush soko1_1.board (locks i) source dir ∨Shape source dir)
 else true
theorem shapes : (List.finRange 2).all (fun i=>(locks i).all (fun source=>allDirs.all (shapeCheck i source)))=true := by decide +kernel
theorem complete (i : Fin 2) (group : List Cell) (bounded : group.length≤3)
 (inside : locks i⊆group) (source : Cell) (owner : source∈group) : source∈locks i := by
 by_cases member : source∈locks i
 ·exact member
 ·have all : source::locks i⊆group := by
   intro c found
   rcases List.mem_cons.mp found with rfl|later
   ·exact owner
   ·exact inside later
  have card := List.Nodup.length_le_of_subset (List.nodup_cons.mpr ⟨member,unique i⟩) all
  simp only [List.length_cons,size i] at card
  omega

theorem head_shape {state : State} {group : List Cell} {dir : Dir} {t : Transition}
 (i : Fin 2) (heroInside : state.player∈region i) (locksInside : locks i⊆group)
 (inside : group⊆state.boulders) (bounded : group.length≤3) (head : step soko1_1.board state dir=some t)
 (pays : OwnedCorral11.PaidStep paid group dir t) :
 ∃source, source∈group ∧t.pushSource=some source ∧Shape source dir := by
 obtain ⟨source,owner,metadata,pays⟩ := pays
 have member := complete i group bounded locksInside source owner
 have adjacent := PairPost11.source_adjacent head metadata
 have behind := Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked state.player
   (step_player_clear _ _ _ _ head).1 dir source adjacent
 have row := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp shapes i (by simp)) source member) dir (Geometry.all_directions dir)
 simp only [shapeCheck,if_pos pays,behind] at row
 rcases of_decide_eq_true row with outside|blocked|shape
 ·exact False.elim (outside heroInside)
 ·exact False.elim (WestRankHead11.source_unblocked head metadata (List.Subset.trans locksInside inside) blocked)
 ·exact ⟨source,owner,metadata,shape⟩

theorem first_cut
 {prior state dirs final pushes moves outcomes priorPushes priorMoves}
 (reached : Trace soko1_1.board soko1_1.initial prior state priorPushes priorMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (group : List Cell) (groupUnique : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤3)
 (good : OwnedCorral11.Good locks region state group) :
 Nonempty (FirstCut paid state group dirs final pushes moves outcomes) := by
 rcases first_cut_or_quiet logged group with found|quiet
 ·exact found
 ·have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
  obtain ⟨i,_,selected⟩ := PairFirstCut11.quiet_good closed unique size quiet valid.1 groupUnique inside bounded good reached.holes_sublist.subset
  have actual := (logged.end_subset valid.1 group groupUnique inside).2
  have card := List.Nodup.length_le_of_subset (unique i) (List.Subset.trans selected actual)
  rw [size i] at card
  have conservation := (reached.append logged.trace).conservation
  have empty : final.holes=[] := completed
  rw [empty] at conservation
  change 18+0=final.boulders.length+16 at conservation
  omega

theorem future_obstruction {beforeDirs state beforePushes beforeMoves before dirs final pushes moves outcomes}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (hero : state.player=239) (front : 265∈state.boulders)
 (markers : ([264,266] : List Cell)⊆endGroup UpperBudget11.Rest before) :
 2≤energy soko1_1.initial final UpperBudget11.Rest (before++outcomes) ∨335≤beforePushes+pushes := by
 let group : List Cell := [264,265,266]
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace
 have restBefore := first.end_subset (by decide) UpperBudget11.Rest (by decide) (by decide)
 have inside : group⊆state.boulders := by
   intro c member
   change c∈([264,265,266] : List Cell) at member
   simp only [List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl
   ·exact restBefore.2 (markers (by decide))
   ·exact front
   ·exact restBefore.2 (markers (by decide))
 have good : OwnedCorral11.Good locks region state group := by
   refine ⟨⟨0,by decide⟩,?_,?_⟩
   ·rw [hero]
    decide +kernel
   ·change ([264,265,266] : List Cell)⊆[264,265,266]
    exact List.Subset.refl _
 obtain ⟨cut⟩ := first_cut first.trace logged completed group (by decide) inside (by decide) good
 have currentGood := PairFirstCut11.quiet_good closed unique size cut.before valid.1 (by decide) inside (by decide) good first.trace.holes_sublist.subset
 obtain ⟨i,heroInside,locksInside⟩ := currentGood
 have selected := cut.before.logged.end_subset valid.1 group (by decide) inside
 have bounded : (endGroup group cut.beforeOutcomes).length≤3 := endGroup_length_le group cut.beforeOutcomes
 obtain ⟨source,owner,metadata,shape⟩ := head_shape i heroInside locksInside selected.2 bounded cut.headChecked cut.headPaid
 let headFirst := first.append cut.before.logged
 have currentValid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant headFirst.trace
 have currentRest := headFirst.end_subset (by decide) UpperBudget11.Rest (by decide) (by decide)
 rcases shape with ⟨rfl,west⟩|⟨rfl,east⟩|⟨rfl,south⟩
 ·have fixed := cut.before.fixed (by decide :264∈group) (by intro dir;exact Or.inl rfl)
  have tag : endGroup [264] cut.beforeOutcomes=[264] := no_push_unchanged _ _ fixed
  have included := end_subset_selected cut.before.logged valid.1 [264] (endGroup UpperBudget11.Rest before)
    (by decide) restBefore.1 (by intro c h;have eq := List.mem_singleton.mp h;subst c;exact markers (by decide)) restBefore.2
  have owns : 264∈endGroup UpperBudget11.Rest (before++cut.beforeOutcomes) := by
    rw [TokenAccounting.endGroup_append]
    exact included (by rw [tag];simp)
  have row := Triangle29111.exit_row currentValid currentRest.1 currentRest.2 cut.headChecked cut.headEffect
    owns metadata (show Triangle29111.paid 264 cut.direction from Or.inl ⟨rfl,west⟩)
  have gap := logged_event_gap_le headFirst cut.headChecked cut.headEffect cut.after UpperBudget11.Rest (by decide) (by decide)
  have equality : before++(cut.beforeOutcomes++cut.headOutcome::cut.afterOutcomes)=before++outcomes := by rw [←cut.outcomesEq]
  have actual : 2≤energy soko1_1.initial final UpperBudget11.Rest (before++outcomes) := by
    have bound := Int.le_trans row gap
    simpa only [List.append_assoc,←cut.outcomesEq,Triangle29111.threshold,if_neg (by decide :¬(264:Cell)=291),if_neg (by decide :¬(266:Cell)=291)] using bound
  exact Or.inl actual
 ·have fixed := cut.before.fixed (by decide :266∈group) (by intro dir;exact Or.inr (Or.inl rfl))
  have tag : endGroup [266] cut.beforeOutcomes=[266] := no_push_unchanged _ _ fixed
  have included := end_subset_selected cut.before.logged valid.1 [266] (endGroup UpperBudget11.Rest before)
    (by decide) restBefore.1 (by intro c h;have eq := List.mem_singleton.mp h;subst c;exact markers (by decide)) restBefore.2
  have owns : 266∈endGroup UpperBudget11.Rest (before++cut.beforeOutcomes) := by
    rw [TokenAccounting.endGroup_append]
    exact included (by rw [tag];simp)
  have row := Triangle29111.exit_row currentValid currentRest.1 currentRest.2 cut.headChecked cut.headEffect
    owns metadata (show Triangle29111.paid 266 cut.direction from Or.inr (Or.inl ⟨rfl,east⟩))
  have gap := logged_event_gap_le headFirst cut.headChecked cut.headEffect cut.after UpperBudget11.Rest (by decide) (by decide)
  have actual : 2≤energy soko1_1.initial final UpperBudget11.Rest (before++outcomes) := by
    simpa only [List.append_assoc,←cut.outcomesEq,Triangle29111.threshold,if_neg (by decide :¬(264:Cell)=291),if_neg (by decide :¬(266:Cell)=291)] using Int.le_trans row gap
  exact Or.inl actual
 ·have target : pushTargets soko1_1.board 291 cut.direction=[317] := by rw [south];decide +kernel
  have eq := UpperHeadCases11.ordinary_effect cut.headChecked cut.headEffect metadata target (by decide +kernel) headFirst.trace.holes_sublist.subset
  have effect : Matches cut.middle cut.actor (.push 291 (.stay 317)) := by simpa only [eq] using cut.headEffect
  have deep := Deep29133511.pushes_lower headFirst (by simpa only [south] using cut.headChecked) effect cut.after completed
  have counts := cut.pushesEq
  change 335≤beforePushes+cut.beforePushes+cut.actor.pushCost+cut.afterPushes at deep
  exact Or.inr (by omega)
#print axioms shapes
#print axioms first_cut
#print axioms future_obstruction
end Owner1007.Gate265Above11
