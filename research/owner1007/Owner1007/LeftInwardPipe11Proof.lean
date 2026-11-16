import Owner1007.LeftInwardPipe11Data
import Owner1007.LeftGateFree11
namespace Owner1007.LeftInwardPipe11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem head_shape {state : State} {dir : Dir} {t : Transition} {source : Cell}
 (i : Fin 6) (hero : state.player∈region i) (physical : locks i⊆state.boulders)
 (pays : paid source dir) (checked : step soko1_1.board state dir=some t)
 (metadata : t.pushSource=some source) : i.val=5∨(source=189∧dir=.west) := by
 have member : source∈([185,187,189,213]:List Cell) := by
  simpa only [paid,List.mem_cons,List.not_mem_nil,or_false] using pays
 have row:=List.all_eq_true.mp (List.all_eq_true.mp (heads i) source member) dir (Geometry.all_directions dir)
 have adjacent:=PairPost11.source_adjacent checked metadata
 have behind:=Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked state.player (floor i hero) dir source adjacent
 simp only [headCheck,behind] at row
 exact of_decide_eq_true row hero (WestRankHead11.source_unblocked checked metadata physical) pays

theorem future_four_with
 (closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid)
 {state final : State} {history dirs : List Dir} {past pastMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (group : List Cell) (uniqueGroup : group.Nodup) (inside : group⊆state.boulders)
 (bounded : group.length≤18) (good : OwnedCorral11.Good locks region state group)
 (gone : endGroup group outcomes=[]) : 4≤energy state final group outcomes := by
 have valid:=NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
 obtain ⟨cut⟩:=Upper216Eight11.first_any closed unique nonempty logged valid.1 uniqueGroup inside good reached.holes_sublist.subset gone
 obtain ⟨i,hero,selected⟩:=Upper216Eight11.quiet_good_any closed unique cut.before valid.1 uniqueGroup inside good reached.holes_sublist.subset
 have beforeReached:=reached.append cut.before.logged.trace
 have beforeValid:=NetHack.SokobanLinearPhases.Map11.trace_phase_invariant beforeReached
 have facts:=cut.before.logged.end_subset valid.1 group uniqueGroup inside
 have physical:=List.Subset.trans selected facts.2
 obtain ⟨source,owner,metadata,pays⟩:=cut.headPaid
 rcases head_shape i hero physical pays cut.headChecked metadata with terminalPhase|west189
 ·have same : i=(5:Fin 6) := Fin.ext terminalPhase
  subst i
  let tail:=Logged.cons cut.headChecked cut.headEffect cut.after
  have currentBound : (endGroup group cut.beforeOutcomes).length≤18 :=
    Nat.le_trans (endGroup_length_le group cut.beforeOutcomes) bounded
  have smallSelected : ([185,187,213]:List Cell)⊆endGroup group cut.beforeOutcomes := selected
  have smallInside := List.Subset.trans smallSelected facts.2
  have bigGone : endGroup (endGroup group cut.beforeOutcomes) (cut.headOutcome::cut.afterOutcomes)=[] := by
   rw [cut.outcomesEq,endGroup_append] at gone
   exact gone
  have smallGone : endGroup [185,187,213] (cut.headOutcome::cut.afterOutcomes)=[] := by
   have sub:=end_subset_selected tail beforeValid.1 [185,187,213] (endGroup group cut.beforeOutcomes)
     (by decide) facts.1 smallSelected facts.2
   rw [bigGone] at sub
   exact List.eq_nil_iff_forall_not_mem.mpr (by intro c member;simpa using sub member)
  have ticket:=LeftGateFree11.future_four beforeReached tail [185,187,213] (by decide) smallInside
    (List.Perm.refl _) hero smallGone
  have compare:=energy_subset beforeReached tail [185,187,213] (endGroup group cut.beforeOutcomes)
    (by decide) facts.1 smallSelected facts.2 currentBound
  have prefixNN:=HeroLedger.Logged.energy_nonnegative cut.before.logged (groupCertificate 18) valid group uniqueGroup inside bounded
  change 0≤energy state cut.middle group cut.beforeOutcomes at prefixNN
  have split:=energy_append state cut.middle final group cut.beforeOutcomes (cut.headOutcome::cut.afterOutcomes)
  have same:=congrArg (energy state final group) cut.outcomesEq
  omega
 ·obtain ⟨rfl,west⟩:=west189
  have checked : step soko1_1.board cut.middle .west=some cut.actor := by simpa only [west] using cut.headChecked
  have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
    (show pushTargets soko1_1.board 189 .west=[188] by decide +kernel) (by decide +kernel) beforeReached.holes_sublist.subset
  have keeps187 : 187∈locks i := by
   have check : ∀i,187∈locks i := by decide +kernel
   exact check i
  have pairBefore : ([187,189]:List Cell)⊆endGroup group cut.beforeOutcomes := by
   intro c member
   rcases List.mem_cons.mp member with rfl|later
   ·exact selected keeps187
   ·have eq : c=189:=List.mem_singleton.mp later
    subst c;exact owner
  have updated:=update_mono [187,189] (endGroup group cut.beforeOutcomes) (by decide) pairBefore cut.headOutcome
  have pair : [187,188]⊆Upper216Eight11.next cut := by
   change [187,188]⊆update (endGroup group cut.beforeOutcomes) cut.headOutcome
   rw [headEq] at updated ⊢
   exact List.Subset.trans (by decide) updated
  have nextFacts:=Upper216Eight11.next_facts cut reached uniqueGroup inside bounded
  have afterReached:=beforeReached.append (Trace.cons cut.headChecked (Trace.nil cut.actor.state))
  exact False.elim (Upper216Eight11.frozen_absurd cut.after (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant afterReached).1
    nextFacts.1 nextFacts.2.1 (Owner1007.locked_of_check _ [187,188] (by decide +kernel))
    (List.Subset.trans pair nextFacts.2.1) (show 188∈[187,188] by decide) (pair (by decide))
    (Upper216Eight11.tail_gone cut gone))
#print axioms head_shape
#print axioms future_four_with
end Owner1007.LeftInwardPipe11
