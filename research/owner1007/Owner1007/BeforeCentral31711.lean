import Owner1007.CentralFirst11Proof
import Owner1007.LowerTrap31819Proof
import Owner1007.UpperLocalPrice11
import Owner1007.WestRankHead11
namespace Owner1007.BeforeCentral31711
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def sources : List Cell := [317]
def westPaid (source : Cell) (dir : Dir) : Prop := source=317∧dir=.west
instance (source : Cell) (dir : Dir) : Decidable (westPaid source dir) := by unfold westPaid;infer_instance
theorem westPaid_source (source : Cell) (dir : Dir) (pays : westPaid source dir) : source∈sources := by rcases pays with ⟨rfl,_⟩;decide
def priceCheck (phase : Nat) : Bool := sources.all fun source => allDirs.all fun dir =>
 if westPaid source dir then match advance soko1_1.board source dir.opposite with
 | none => false
 | some hero => (pushTargets soko1_1.board source dir).all fun dest =>
   decide (dest∉soko1_1.initial.holes ∧ 1≤ActorPrices11.price phase hero source dest)
 else true
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem prices : (List.range 16).all priceCheck=true := by decide +kernel
theorem price_row (phase : Nat) (active : phase<16) (hero source dest : Cell) (dir : Dir)
 (pays : westPaid source dir) (behind : advance soko1_1.board source dir.opposite=some hero)
 (target : dest∈pushTargets soko1_1.board source dir) :
 dest∉soko1_1.initial.holes ∧ 1≤ActorPrices11.price phase hero source dest := by
 have a := List.all_eq_true.mp prices phase (List.mem_range.mpr active)
 have b := List.all_eq_true.mp (List.all_eq_true.mp a source (westPaid_source source dir pays)) dir (Geometry.all_directions dir)
 simp only [if_pos pays,behind] at b
 exact of_decide_eq_true (List.all_eq_true.mp b dest target)

theorem west_row {state : State} {dir : Dir} {t : Transition} {outcome : Outcome} {group : List Cell}
 (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state)
 (unique : group.Nodup) (inside : group⊆state.boulders)
 (head : step soko1_1.board state dir=some t) (effect : Matches state t outcome)
 (pays : OwnedCorral11.PaidStep westPaid group dir t) :
 1≤charge NetHack.Soko11Hero315.holeWeight group outcome+value t.state (update group outcome)-value state group := by
 obtain ⟨source,owner,metadata,pays⟩ := pays
 rcases step_cases_full _ _ _ _ head with walked|pushed
 · obtain ⟨target,_,_,_,_,shape⟩ := walked
   simp only [shape] at metadata
   contradiction
 · obtain ⟨other,result,adjacent,_,_,push,shape⟩ := pushed
   have same : other=source := by simpa only [shape,Option.some.injEq] using metadata
   subst other
   have reverse := Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked state.player
     (step_player_clear _ _ _ _ head).1 dir source adjacent
   obtain ⟨phase,atIndex⟩ := valid.2
   have phaseEq := HazardPhaseCountedCorrection.at_phase NetHack.SokobanLinearPhases.Map11.certificate phase state atIndex
   have within : HazardPhases.At NetHack.SokobanLinearPhases.Map11.certificate
       (HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state) state := by rw [←phaseEq]; exact atIndex
   have active : HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state<16 :=
     HazardPhaseCountedCorrection.active_of_step _ _ within _ _ head
   have spec := pushBoulder_spec _ _ _ _ _ push
   have row := price_row _ active state.player source result.landing dir pays reverse spec.2
   have holesInside : state.holes⊆soko1_1.initial.holes := by rw [atIndex.2.1]; exact (List.drop_sublist phase _).subset
   have unfilled : result.filled=none := by
     rcases spec.1 with stay|fill
     · exact stay.1
     · exact False.elim (row.1 (holesInside fill.2.1))
   have landed : t.landing=some result.landing := by simp only [shape]
   have noFill : t.filled=none := by simpa only [shape] using unfilled
   have sameOutcome := CutStrict11.outcome_stay effect metadata landed noFill
   subst outcome
   exact OwnedStrict11.owned_stay_bound scalar state dir t valid head source result.landing effect group unique inside owner 1 row.2
#print axioms prices
#print axioms west_row


def directionCheck (dir : Dir) : Bool :=
 match advance soko1_1.board 317 dir.opposite with
 |none=>true
 |some hero=>decide (hero∉soko1_1.board.floor ∨BlockedPush soko1_1.board [317] 317 dir ∨dir=.east∨dir=.west)
theorem directions : allDirs.all directionCheck=true := by decide +kernel
theorem head_shape {state : State} {dir : Dir} {t : Transition}
 (member : 317∈state.boulders) (head : step soko1_1.board state dir=some t) (metadata : t.pushSource=some 317) :
 dir=.east∨dir=.west := by
 have adjacent := PairPost11.source_adjacent head metadata
 have floor := (step_player_clear _ _ _ _ head).1
 have behind := Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked state.player floor dir 317 adjacent
 have row := List.all_eq_true.mp directions dir (Geometry.all_directions dir)
 simp only [directionCheck,behind] at row
 rcases of_decide_eq_true row with outside|blocked|east|west
 · exact False.elim (outside floor)
 · exact False.elim (WestRankHead11.source_unblocked head metadata (by simpa using member) blocked)
 · exact Or.inl east
 · exact Or.inr west
def firstPaid (source : Cell) (_ : Dir) : Prop := source=317
instance (source : Cell) (dir : Dir) : Decidable (firstPaid source dir) := by unfold firstPaid;infer_instance
#print axioms head_shape

open Owner1007.UpperFirstCut11
theorem stationary_before
 (centralClosed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes CentralFirst11.locks CentralFirst11.region CentralFirst11.paid)
 (trapClosed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes LowerTrap31819.locks LowerTrap31819.region LowerTrap31819.paid)
 {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes) (completed : Goal final)
 (zeroRest : energy soko1_1.initial final UpperBudget11.Rest outcomes=0)
 (stationary321 : ownPushes [321] outcomes=0)
 (central : FirstCut CentralFirst11.paid soko1_1.initial CentralFirst11.sources dirs final pushes moves outcomes) :
 ownPushes [317] central.beforeOutcomes=0 := by
 rcases first_cut_or_quiet (paid:=firstPaid) central.before.logged [317] with found|quiet
 · obtain ⟨first⟩ := found
   have fixed317 := first.before.fixed (by simp :317∈([317] : List Cell)) (fun _=>rfl)
   have tag317 : endGroup [317] first.beforeOutcomes=[317] := no_push_unchanged _ _ fixed317
   obtain ⟨source,owner,metadata,same⟩ := first.headPaid
   change source=317 at same
   subst source
   have selected317 := first.before.logged.end_subset (by decide) [317] (by decide) (by decide)
   have actual317 : 317∈first.middle.boulders := by rw [tag317] at selected317;exact selected317.2 (by simp)
   let last := first.after.append (Logged.cons central.headChecked central.headEffect central.after)
   have allEffects : first.beforeOutcomes++first.headOutcome::(first.afterOutcomes++central.headOutcome::central.afterOutcomes)=outcomes := by
     calc
       _=(first.beforeOutcomes++first.headOutcome::first.afterOutcomes)++central.headOutcome::central.afterOutcomes := by simp only [List.append_assoc,List.cons_append]
       _=central.beforeOutcomes++central.headOutcome::central.afterOutcomes :=
         congrArg (fun before=>before++central.headOutcome::central.afterOutcomes) first.outcomesEq.symm
       _=outcomes := central.outcomesEq.symm
   have beforeValid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.before.logged.trace
   have restSelected := first.before.logged.end_subset (by decide) UpperBudget11.Rest (by decide) (by decide)
   have included317 := end_subset_selected first.before.logged (by decide) [317] UpperBudget11.Rest
     (by decide) (by decide) (by decide) (by decide)
   have owner317 : 317∈endGroup UpperBudget11.Rest first.beforeOutcomes := included317 (by rw [tag317];simp)
   rcases head_shape actual317 first.headChecked metadata with east|west
   · have target : pushTargets soko1_1.board 317 first.direction=[318] := by rw [east];decide +kernel
     have headEq := UpperHeadCases11.ordinary_effect first.headChecked first.headEffect metadata target (by decide +kernel) first.before.logged.trace.holes_sublist.subset
     have effect : Matches first.middle first.actor (.push 317 (.stay 318)) := by simpa only [headEq] using first.headEffect
     have centralZero (cell : Cell) (member : cell∈CentralFirst11.sources) : ownPushes [cell] central.beforeOutcomes=0 :=
       central.before.fixed member (fun _=>member)
     have beforeZero (cell : Cell) (member : cell∈([266,268,293,321] : List Cell)) : ownPushes [cell] first.beforeOutcomes=0 := by
       have prefixZeroValue : ownPushes [cell] central.beforeOutcomes=0 := by
         simp only [List.mem_cons,List.not_mem_nil,or_false] at member
         rcases member with rfl|rfl|rfl|rfl
         · exact centralZero 266 (by decide)
         · exact centralZero 268 (by decide)
         · exact centralZero 293 (by decide)
         · have whole := stationary321
           rw [central.outcomesEq,ownPushes_append] at whole
           omega
       rw [first.outcomesEq,ownPushes_append] at prefixZeroValue
       omega
     have beforeMember (cell : Cell) (member : cell∈([266,268,293,321] : List Cell)) : cell∈endGroup UpperBudget11.Rest first.beforeOutcomes := by
       have tag : endGroup [cell] first.beforeOutcomes=[cell] := no_push_unchanged _ _ (beforeZero cell member)
       have sourceRest : cell∈UpperBudget11.Rest := (show ([266,268,293,321] : List Cell)⊆UpperBudget11.Rest from by decide) member
       have subset : [cell]⊆UpperBudget11.Rest := by simpa using sourceRest
       have included := end_subset_selected first.before.logged (by decide) [cell] UpperBudget11.Rest
         (by simp) (by decide) subset (by decide)
       exact included (by rw [tag];simp)
     let headLog : Logged soko1_1.board first.middle [first.direction] first.actor.state first.actor.pushCost 1 [first.headOutcome] :=
       .cons first.headChecked first.headEffect (.nil _)
     let toState := first.before.logged.append headLog
     have good : OwnedCorral11.Good LowerTrap31819.locks LowerTrap31819.region first.actor.state
         (endGroup UpperBudget11.Rest (first.beforeOutcomes++[first.headOutcome])) := by
       refine ⟨⟨0,by decide⟩,?_,?_⟩
       · have hero : first.actor.state.player=317 := by rw [effect.2]
         rw [hero];decide +kernel
       · intro c member
         have cases : c=266∨c=268∨c=293∨c=318∨c=321 := by simpa [LowerTrap31819.locks] using member
         rw [endGroup_append]
         change c∈update (endGroup UpperBudget11.Rest first.beforeOutcomes) first.headOutcome
         rw [headEq]
         simp only [update,move,if_pos owner317,post]
         rcases cases with rfl|rfl|rfl|rfl|rfl
         · exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne (by decide :266≠317)).mpr (beforeMember 266 (by decide)))
         · exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne (by decide :268≠317)).mpr (beforeMember 268 (by decide)))
         · exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne (by decide :293≠317)).mpr (beforeMember 293 (by decide)))
         · exact List.mem_cons_self
         · exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne (by decide :321≠317)).mpr (beforeMember 321 (by decide)))
     have cost := LowerTrap31819.rest_positive trapClosed toState last completed good
     have allEffects' : (first.beforeOutcomes++[first.headOutcome])++(first.afterOutcomes++central.headOutcome::central.afterOutcomes)=outcomes := by
       simpa only [List.append_assoc,List.cons_append,List.nil_append] using allEffects
     change 2≤energy soko1_1.initial final UpperBudget11.Rest ((first.beforeOutcomes++[first.headOutcome])++(first.afterOutcomes++central.headOutcome::central.afterOutcomes)) at cost
     rw [allEffects'] at cost
     omega
   · have row := west_row beforeValid restSelected.1 restSelected.2 first.headChecked first.headEffect
       ⟨317,owner317,metadata,⟨rfl,west⟩⟩
     have bound := logged_event_gap_le first.before.logged first.headChecked first.headEffect last UpperBudget11.Rest (by decide) (by decide)
     change charge NetHack.Soko11Hero315.holeWeight (endGroup UpperBudget11.Rest first.beforeOutcomes) first.headOutcome+
       value first.actor.state (update (endGroup UpperBudget11.Rest first.beforeOutcomes) first.headOutcome)-
       value first.middle (endGroup UpperBudget11.Rest first.beforeOutcomes)≤
       energy soko1_1.initial final UpperBudget11.Rest (first.beforeOutcomes++first.headOutcome::(first.afterOutcomes++central.headOutcome::central.afterOutcomes)) at bound
     rw [allEffects] at bound
     omega
 · exact quiet.fixed (by simp :317∈([317] : List Cell)) (fun _=>rfl)
#print axioms stationary_before

end Owner1007.BeforeCentral31711
