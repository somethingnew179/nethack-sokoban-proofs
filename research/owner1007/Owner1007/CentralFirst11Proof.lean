import Owner1007.CentralFirst11Data
import Owner1007.CentralFirst11Prices
import Owner1007.WestRankHead11
import Owner1007.QuietFixed11
import Owner1007.LoggedEventGap11
import Owner1007.UpperBudget11
namespace Owner1007.CentralFirst11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def shapeCheck (source : Cell) (dir : Dir) : Bool :=
 match advance soko1_1.board source dir.opposite with
 |none=>true
 |some hero=>decide (hero∉region 0 ∨BlockedPush soko1_1.board (locks 0) source dir ∨Shape source dir)
theorem shapes : sources.all (fun source=>allDirs.all (shapeCheck source))=true := by decide +kernel
theorem head_shape {state : State} {dir : Dir} {t : Transition} {source : Cell}
 (heroInside : state.player∈region 0) (locksInside : locks 0⊆state.boulders)
 (member : source∈sources) (head : step soko1_1.board state dir=some t) (metadata : t.pushSource=some source) :
 Shape source dir := by
 have adjacent := PairPost11.source_adjacent head metadata
 have behind := Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked state.player
   (step_player_clear _ _ _ _ head).1 dir source adjacent
 have row := List.all_eq_true.mp (List.all_eq_true.mp shapes source member) dir (Geometry.all_directions dir)
 simp only [shapeCheck,behind] at row
 rcases of_decide_eq_true row with outside|blocked|shape
 · exact False.elim (outside heroInside)
 · exact False.elim (WestRankHead11.source_unblocked head metadata locksInside blocked)
 · exact shape
theorem frozen : Owner1007.Locked soko1_1.board [266,267] := Owner1007.locked_of_check _ _ (by decide +kernel)

theorem stays266 {beforeDirs state beforePushes beforeMoves before source t afterDirs final afterPushes afterMoves after}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (effect : Matches state t (.push source (.stay 267)))
 (last : Logged soko1_1.board t.state afterDirs final afterPushes afterMoves after)
 (stationary : ownPushes [266] before=0) (different : source≠266) :
 endGroup [266] (before++.push source (.stay 267)::after)≠[] := by
 have tag : endGroup [266] before=[266] := no_push_unchanged _ _ stationary
 have selected := first.end_subset (by decide) [266] (by decide) (by decide)
 have retained : 266∈state.boulders := by rw [tag] at selected;exact selected.2 (by simp)
 have inside : [266,267]⊆t.state.boulders := by
   rw [effect.2]
   intro c member
   simp only [List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl
   · exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne different.symm).mpr retained)
   · exact List.mem_cons_self
 have fixed := locked_identity last frozen inside (by decide :266∈([266,267] : List Cell))
 have outside : source∉([266] : List Cell) := by simpa using different
 rw [endGroup_append,tag]
 simpa only [endGroup,update,move,if_neg outside] using (show endGroup [266] after≠[] by rw [fixed];simp)

theorem first_cut
 (closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid)
 {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes) (completed : Goal final) :
 Nonempty (FirstCut paid soko1_1.initial sources dirs final pushes moves outcomes) := by
 have good : OwnedCorral11.Good locks region soko1_1.initial sources := by
   refine ⟨0,?_,?_⟩ <;> decide +kernel
 rcases first_cut_or_quiet logged sources with found|quiet
 · exact found
 · have unique : ∀i,(locks i).Nodup := by intro i;change sources.Nodup;decide
   have size : ∀i,(locks i).length=3 := by intro i;rfl
   have finalGood := PairFirstCut11.quiet_good closed unique size quiet (by decide) (by decide) (by decide) (by decide) good (by simp)
   obtain ⟨i,_,selected⟩ := finalGood
   have actual := (logged.end_subset (by decide) sources (by decide) (by decide)).2
   have card := List.Nodup.length_le_of_subset (unique i) (List.Subset.trans selected actual)
   rw [size i] at card
   have conservation := logged.trace.conservation
   have empty : final.holes=[] := completed
   rw [empty] at conservation
   change 18+0=final.boulders.length+16 at conservation
   omega

theorem first_west
 (closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid)
 {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes) (completed : Goal final)
 (zeroRest : energy soko1_1.initial final UpperBudget11.Rest outcomes=0)
 (cut : FirstCut paid soko1_1.initial sources dirs final pushes moves outcomes) :
 cut.actor.pushSource=some 293 ∧cut.direction=.west ∧cut.headOutcome=.push 293 (.stay 292) := by
 have unique : ∀i,(locks i).Nodup := by intro i;change sources.Nodup;decide
 have size : ∀i,(locks i).length=3 := by intro i;rfl
 have good : OwnedCorral11.Good locks region soko1_1.initial sources := by
   refine ⟨0,?_,?_⟩ <;> decide +kernel
 have currentGood := PairFirstCut11.quiet_good closed unique size cut.before (by decide) (by decide) (by decide) (by decide) good (by simp)
 obtain ⟨node,heroInside,locksInside⟩ := currentGood
 have currentSelected := cut.before.logged.end_subset (by decide) sources (by decide) (by decide)
 have actualLocks := List.Subset.trans locksInside currentSelected.2
 obtain ⟨source,owner,metadata,known⟩ := cut.headPaid
 have shape := head_shape heroInside actualLocks known cut.headChecked metadata
 have beforeValid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant cut.before.logged.trace
 have fixed (cell : Cell) (member : cell∈sources) : ownPushes [cell] cut.beforeOutcomes=0 :=
   cut.before.fixed member (fun _=>member)
 have exclude_survivor (survives : endGroup [266] outcomes≠[]) : False := by
   have single := survivor_energy logged completed 266 survives
   have debt : value soko1_1.initial [266]≤-19 := by decide +kernel
   have bound := energy_subset (Trace.nil soko1_1.initial) logged [266] UpperBudget11.Rest
     (by decide) (by decide) (by decide) (by decide) (by decide)
   have nn : (0:Int)≤Int.ofNat (ownPushes [266] outcomes) := Int.ofNat_nonneg _
   omega
 have exclude_freeze (source : Cell) (different : source≠266)
     (headEq : cut.headOutcome=.push source (.stay 267)) : False := by
   have effect : Matches cut.middle cut.actor (.push source (.stay 267)) := by simpa only [headEq] using cut.headEffect
   have survives := stays266 cut.before.logged effect cut.after (fixed 266 (by decide)) different
   have allEffects := cut.outcomesEq
   rw [headEq] at allEffects
   apply exclude_survivor
   rw [allEffects]
   exact survives
 rcases shape with positive|⟨rfl,west⟩|⟨rfl,west⟩|⟨rfl,north⟩
 · have tag : endGroup [source] cut.beforeOutcomes=[source] := no_push_unchanged _ _ (fixed source known)
   have sourceRest : source∈UpperBudget11.Rest := (show sources⊆UpperBudget11.Rest from by decide) known
   have subset : [source]⊆UpperBudget11.Rest := by simpa using sourceRest
   have included := end_subset_selected cut.before.logged (by decide) [source] UpperBudget11.Rest
     (by simp) (by decide) subset (by decide)
   have restSelected := cut.before.logged.end_subset (by decide) UpperBudget11.Rest (by decide) (by decide)
   have row := exit_row beforeValid restSelected.1 restSelected.2 cut.headChecked cut.headEffect
     ⟨source,included (by rw [tag];simp),metadata,positive⟩
   have bound := logged_event_gap_le cut.before.logged cut.headChecked cut.headEffect cut.after UpperBudget11.Rest (by decide) (by decide)
   rw [←cut.outcomesEq] at bound
   omega
 · have target : pushTargets soko1_1.board 293 cut.direction=[292] := by rw [west];decide +kernel
   have head := UpperHeadCases11.ordinary_effect cut.headChecked cut.headEffect metadata target (by decide +kernel) cut.before.logged.trace.holes_sublist.subset
   exact ⟨metadata,west,head⟩
 · have target : pushTargets soko1_1.board 268 cut.direction=[267] := by rw [west];decide +kernel
   have head := UpperHeadCases11.ordinary_effect cut.headChecked cut.headEffect metadata target (by decide +kernel) cut.before.logged.trace.holes_sublist.subset
   exact False.elim (exclude_freeze 268 (by decide) head)
 · have target : pushTargets soko1_1.board 293 cut.direction=[267] := by rw [north];decide +kernel
   have head := UpperHeadCases11.ordinary_effect cut.headChecked cut.headEffect metadata target (by decide +kernel) cut.before.logged.trace.holes_sublist.subset
   exact False.elim (exclude_freeze 293 (by decide) head)
#print axioms first_west
end Owner1007.CentralFirst11
