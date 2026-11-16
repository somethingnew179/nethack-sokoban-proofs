import Owner1007.UpperEightExit11
import Owner1007.UpperSixBudget11
import Owner1007.Upper216After11
import Owner1007.RightFour11
import Owner1007.UpperConsumedFuture11
namespace Owner1007.Upper216Eight11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
open Owner1007.UpperBudget11 Owner1007.UpperCutBudget11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def locks1 (_ : Fin 1) : List Cell := [191,193,218]
def region1 (_ : Fin 1) : List Cell := RightFour11.region 0
def paid1 (source : Cell) (dir : Dir) : Prop := (source=191 ∨ source=218) ∧ dir=.east
instance (c : Cell) (d : Dir) : Decidable (paid1 c d) := by unfold paid1; infer_instance
def locks2 (_ : Fin 1) : List Cell := [193,219]
def region2 (_ : Fin 1) : List Cell := PostCuts11.without PostCuts11.H [193,194,219,220]
def paid2 (source : Cell) (dir : Dir) : Prop := (source=193 ∨ source=219) ∧ dir=.east
instance (c : Cell) (d : Dir) : Decidable (paid2 c d) := by unfold paid2; infer_instance

theorem check1 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks1 region1 paid1 0=true := by decide +kernel
theorem check2 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks2 region2 paid2 0=true := by decide +kernel
theorem floor1 (i : Fin 1) : region1 i⊆soko1_1.board.floor := RightFour11.floor 0
theorem floor2 (i : Fin 1) : region2 i⊆soko1_1.board.floor := by
 have row : (region2 0).all (fun c=>decide (c∈soko1_1.board.floor))=true := by decide +kernel
 intro c h
 exact of_decide_eq_true (List.all_eq_true.mp row c h)
theorem closed1 : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks1 region1 paid1 := by
 apply FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked floor1
 intro i
 have same : i=0 := Fin.ext (by omega)
 simpa only [same] using check1
theorem closed2 : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks2 region2 paid2 := by
 apply FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked floor2
 intro i
 have same : i=0 := Fin.ext (by omega)
 simpa only [same] using check2

def priceRows (phase : Nat) : Bool :=
 decide (2≤ActorPrices11.price phase 192 193 194) &&
 decide (2≤ActorPrices11.price phase 218 219 220)
theorem prices2 : (List.range 16).all priceRows=true := by decide +kernel
#print axioms check1
#print axioms check2
#print axioms prices2

theorem quiet_good_any {n : Nat} {ls rs : Fin n→List Cell} {paid : Cell→Dir→Prop}
 (closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes ls rs paid)
 (uni : ∀i, (ls i).Nodup)
 {state final : State} {group : List Cell} {dirs : List Dir} {pushes moves : Nat} {outcomes : List Outcome}
 (quiet : UpperQuiet11.Quiet paid state group dirs final pushes moves outcomes)
 (actual : state.boulders.Nodup) (unique : group.Nodup) (inside : group⊆state.boulders)
 (good : OwnedCorral11.Good ls rs state group)
 (holes : state.holes⊆soko1_1.initial.holes) :
 OwnedCorral11.Good ls rs final (endGroup group outcomes) := by
 induction quiet with
 | nil => exact good
 | @cons state group dir t rest final pushes moves outcome outcomes checked effect avoid tail ih =>
   have nextActual := step_boulders_nodup _ _ _ _ actual checked
   have nextUnique := GhostSubset.update_unique _ _ _ effect nextActual group unique inside
   have nextInside := GhostSubset.update_subset _ _ _ effect group unique inside
   have nextGood := OwnedCorralAny11.step_good_except closed uni good inside holes checked effect avoid
   have nextHoles := List.Subset.trans (step_holes_sublist _ _ _ _ checked).subset holes
   exact ih nextActual nextUnique nextInside nextGood nextHoles

theorem first_any {n : Nat} {ls rs : Fin n→List Cell} {paid : Cell→Dir→Prop}
 (closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes ls rs paid)
 (uni : ∀i, (ls i).Nodup) (nonempty : ∀i, ls i≠[])
 {state final : State} {group : List Cell} {dirs : List Dir} {pushes moves : Nat} {outcomes : List Outcome}
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (actual : state.boulders.Nodup) (unique : group.Nodup) (inside : group⊆state.boulders)
 (good : OwnedCorral11.Good ls rs state group)
 (holes : state.holes⊆soko1_1.initial.holes) (gone : endGroup group outcomes=[]) :
 Nonempty (FirstCut paid state group dirs final pushes moves outcomes) := by
 rcases first_cut_or_quiet logged group with found|quiet
 · exact found
 · obtain ⟨i,_,sub⟩ := quiet_good_any closed uni quiet actual unique inside good holes
   rw [gone] at sub
   exact False.elim (nonempty i (List.eq_nil_iff_forall_not_mem.mpr (by intro c h; simpa using sub h)))

def next {paid state group dirs final pushes moves outcomes}
 (cut : FirstCut paid state group dirs final pushes moves outcomes) :=
 update (endGroup group cut.beforeOutcomes) cut.headOutcome

theorem next_facts {paid state group dirs final pushes moves outcomes history past pastMoves}
 (cut : FirstCut paid state group dirs final pushes moves outcomes)
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (unique : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤18) :
 (next cut).Nodup ∧ next cut⊆cut.actor.state.boulders ∧ (next cut).length≤18 := by
 have actual := (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached).1
 have before := cut.before.logged.end_subset actual group unique inside
 have current := (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant (reached.append cut.before.logged.trace)).1
 have afterActual := step_boulders_nodup _ _ _ _ current cut.headChecked
 have unq := GhostSubset.update_unique _ _ _ cut.headEffect afterActual _ before.1 before.2
 have sub := GhostSubset.update_subset _ _ _ cut.headEffect _ before.1 before.2
 have lenBefore := endGroup_length_le group cut.beforeOutcomes
 have lenAfter := update_length (endGroup group cut.beforeOutcomes) cut.headOutcome
 exact ⟨unq,sub,by change (update (endGroup group cut.beforeOutcomes) cut.headOutcome).length≤18; omega⟩

theorem tail_gone {paid state group dirs final pushes moves outcomes}
 (cut : FirstCut paid state group dirs final pushes moves outcomes)
 (gone : endGroup group outcomes=[]) : endGroup (next cut) cut.afterOutcomes=[] := by
 rw [cut.outcomesEq,endGroup_append] at gone
 exact gone

theorem two_tail {paid state group dirs final pushes moves outcomes history past pastMoves}
 (cut : FirstCut paid state group dirs final pushes moves outcomes)
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (unique : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤18)
 (row : 2≤charge NetHack.Soko11Hero315.holeWeight (endGroup group cut.beforeOutcomes) cut.headOutcome+
   value cut.actor.state (next cut)-value cut.middle (endGroup group cut.beforeOutcomes)) :
 2+energy cut.actor.state final (next cut) cut.afterOutcomes≤energy state final group outcomes := by
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
 have nn := HeroLedger.Logged.energy_nonnegative cut.before.logged (groupCertificate 18) valid group unique inside bounded
 change 0≤energy state cut.middle group cut.beforeOutcomes at nn
 have split := energy_append state cut.middle final group cut.beforeOutcomes (cut.headOutcome::cut.afterOutcomes)
 have one := OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight cut.middle cut.actor.state final
   (endGroup group cut.beforeOutcomes) cut.headOutcome cut.afterOutcomes
 change energy cut.middle final (endGroup group cut.beforeOutcomes) (cut.headOutcome::cut.afterOutcomes)=
   charge NetHack.Soko11Hero315.holeWeight (endGroup group cut.beforeOutcomes) cut.headOutcome+
   value cut.actor.state (next cut)-value cut.middle (endGroup group cut.beforeOutcomes)+
   energy cut.actor.state final (next cut) cut.afterOutcomes at one
 have same := congrArg (energy state final group) cut.outcomesEq
 omega

theorem frozen_absurd {state final : State} {group locked : List Cell} {cell : Cell}
 {dirs : List Dir} {pushes moves : Nat} {outcomes : List Outcome}
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (actual : state.boulders.Nodup) (unique : group.Nodup) (inside : group⊆state.boulders)
 (frozen : Owner1007.Locked soko1_1.board locked) (phys : locked⊆state.boulders)
 (mem : cell∈locked) (owns : cell∈group) (gone : endGroup group outcomes=[]) : False := by
 have fixed := locked_identity logged frozen phys mem
 have sub := logged.end_mono actual [cell] group (by simp) (by simpa using phys mem)
   (by intro c h; have same : c=cell:=List.mem_singleton.mp h; exact same ▸ owns)
 rw [fixed,gone] at sub
 simpa using sub (by simp : cell∈[cell])

theorem exit2 {state : State} {dir : Dir} {t : Transition} {outcome : Outcome} {group : List Cell}
 (good : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state)
 (checked : step soko1_1.board state dir=some t) (effect : Matches state t outcome)
 (unique : group.Nodup) (inside : group⊆state.boulders)
 (pays : OwnedCorral11.PaidStep paid2 group dir t) :
 2≤charge NetHack.Soko11Hero315.holeWeight group outcome+
   value t.state (update group outcome)-value state group := by
 obtain ⟨source,owner,metadata,pays⟩ := pays
 obtain ⟨phase,atIndex⟩ := good.2
 have phaseEq := HazardPhaseCountedCorrection.at_phase NetHack.SokobanLinearPhases.Map11.certificate phase state atIndex
 have within : HazardPhases.At NetHack.SokobanLinearPhases.Map11.certificate
     (HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state) state := by rw [←phaseEq]; exact atIndex
 have active : HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state<16 :=
   HazardPhaseCountedCorrection.active_of_step _ _ within _ _ checked
 have holesInside : state.holes⊆soko1_1.initial.holes := by
   rw [atIndex.2.1]
   exact (List.drop_sublist phase _).subset
 have row := Bool.and_eq_true_iff.mp (List.all_eq_true.mp prices2 _ (List.mem_range.mpr active))
 rcases pays with ⟨rfl|rfl,rfl⟩
 · have same := UpperHeadCases11.ordinary_effect checked effect metadata
     (show pushTargets soko1_1.board 193 .east=[194] by decide +kernel) (by decide +kernel) holesInside
   subst outcome
   have hero := ActorPrices11.support_of_check 193 state.player .east 192 (by decide +kernel)
     (step_player_clear _ _ _ _ checked).1 (RightFour11.east_support checked metadata)
   have cost := of_decide_eq_true row.1
   have price : 2≤1+scalar.weight (HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state) 193 194 -
       scalar.weight (HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state) state.player 193 := by
     rw [hero]; exact cost
   exact OwnedStrict11.owned_stay_bound scalar state .east t good checked 193 194 effect group unique inside owner 2 price
 · have same := UpperHeadCases11.ordinary_effect checked effect metadata
     (show pushTargets soko1_1.board 219 .east=[220] by decide +kernel) (by decide +kernel) holesInside
   subst outcome
   have hero := ActorPrices11.support_of_check 219 state.player .east 218 (by decide +kernel)
     (step_player_clear _ _ _ _ checked).1 (RightFour11.east_support checked metadata)
   have cost := of_decide_eq_true row.2
   have price : 2≤1+scalar.weight (HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state) 219 220 -
       scalar.weight (HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state) state.player 219 := by
     rw [hero]; exact cost
   exact OwnedStrict11.owned_stay_bound scalar state .east t good checked 219 220 effect group unique inside owner 2 price

theorem future_two {state final : State} {history dirs : List Dir} {past pastMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (group : List Cell) (unique : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤18)
 (good : OwnedCorral11.Good locks2 region2 state group) (gone : endGroup group outcomes=[]) :
 2≤energy state final group outcomes := by
 have priced : ∀ state dir t outcome group,
     HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state →
     group.Nodup → group⊆state.boulders → group.length≤18 →
     step soko1_1.board state dir=some t → Matches state t outcome →
     OwnedCorral11.PaidStep paid2 group dir t →
     2≤charge (groupCertificate 18).holeWeight group outcome+
       (groupCertificate 18).groupValue t.state (update group outcome)-(groupCertificate 18).groupValue state group := by
   intro state dir t outcome group valid unique inside bounded checked effect pays
   exact exit2 valid checked effect unique inside pays
 exact OwnedCorralAny11.energy_if_empty closed2 (by decide +kernel) (by decide +kernel)
   (groupCertificate 18) 2 priced logged (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached)
   group unique inside bounded good reached.holes_sublist.subset gone


theorem future_four {state final : State} {history dirs : List Dir} {past pastMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (group : List Cell) (unique : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤18)
 (good : OwnedCorral11.Good locks1 region1 state group) (gone : endGroup group outcomes=[]) :
 4≤energy state final group outcomes := by
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
 obtain ⟨cut⟩ := first_any closed1 (by decide +kernel) (by decide +kernel) logged valid.1 unique inside good reached.holes_sublist.subset gone
 obtain ⟨i,heroBefore,locksBefore⟩ := quiet_good_any closed1 (by decide +kernel) cut.before valid.1 unique inside good reached.holes_sublist.subset
 have beforeLocks : [191,193,218]⊆endGroup group cut.beforeOutcomes := locksBefore
 have beforeReached := reached.append cut.before.logged.trace
 have beforeValid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant beforeReached
 have beforeFacts := cut.before.logged.end_subset valid.1 group unique inside
 have afterFacts := next_facts cut reached unique inside bounded
 have afterReached := beforeReached.append (Trace.cons cut.headChecked (Trace.nil cut.actor.state))
 have afterGone := tail_gone cut gone
 obtain ⟨source,owner,metadata,pays⟩ := cut.headPaid
 have row := RightFour11.exit_row beforeValid cut.headChecked cut.headEffect beforeFacts.1 beforeFacts.2
   (show OwnedCorral11.PaidStep RightFour11.paid (endGroup group cut.beforeOutcomes) cut.direction cut.actor from
     ⟨source,owner,metadata,pays⟩)
 change 2≤charge NetHack.Soko11Hero315.holeWeight (endGroup group cut.beforeOutcomes) cut.headOutcome+
   value cut.actor.state (next cut)-value cut.middle (endGroup group cut.beforeOutcomes) at row
 have sum := two_tail cut reached unique inside bounded row
 rcases pays with ⟨rfl|rfl,directionEq⟩
 · have checked : step soko1_1.board cut.middle .east=some cut.actor := by simpa only [directionEq] using cut.headChecked
   have headEq := UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
     (show pushTargets soko1_1.board 191 .east=[192] by decide +kernel) (by decide +kernel) beforeReached.holes_sublist.subset
   have selected := update_mono [191,193,218] (endGroup group cut.beforeOutcomes) (by decide) beforeLocks cut.headOutcome
   have pair : [192,193]⊆next cut := by
     have small : [192,193]⊆update [191,193,218] (.push 191 (.stay 192)) := by decide
     rw [headEq] at selected
     change _ ⊆ update (endGroup group cut.beforeOutcomes) cut.headOutcome
     rw [headEq]
     exact List.Subset.trans small selected
   have physical : [192,193]⊆cut.actor.state.boulders := List.Subset.trans pair afterFacts.2.1
   exact False.elim (frozen_absurd cut.after (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant afterReached).1
     afterFacts.1 afterFacts.2.1 (Owner1007.locked_of_check _ [192,193] (by decide +kernel)) physical
     (show 192∈[192,193] by decide) (pair (by decide)) afterGone)
 · have checked : step soko1_1.board cut.middle .east=some cut.actor := by simpa only [directionEq] using cut.headChecked
   have headEq := UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
     (show pushTargets soko1_1.board 218 .east=[219] by decide +kernel) (by decide +kernel) beforeReached.holes_sublist.subset
   have effect : Matches cut.middle cut.actor (.push 218 (.stay 219)) := by simpa only [headEq] using cut.headEffect
   have selected := update_mono [191,193,218] (endGroup group cut.beforeOutcomes) (by decide) beforeLocks cut.headOutcome
   have pair : [193,219]⊆next cut := by
     have small : [193,219]⊆update [191,193,218] (.push 218 (.stay 219)) := by decide
     rw [headEq] at selected
     change _ ⊆ update (endGroup group cut.beforeOutcomes) cut.headOutcome
     rw [headEq]
     exact List.Subset.trans small selected
   have hero : cut.actor.state.player=218 := by rw [effect.2]
   have nextGood : OwnedCorral11.Good locks2 region2 cut.actor.state (next cut) := by
     refine ⟨0,?_,pair⟩
     rw [hero]; decide +kernel
   have tail := future_two afterReached cut.after (next cut) afterFacts.1 afterFacts.2.1 afterFacts.2.2 nextGood afterGone
   omega
#print axioms future_four

theorem future_six {state final : State} {history dirs : List Dir} {past pastMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (group : List Cell) (unique : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤18)
 (good : OwnedCorral11.Good RightFour11.locks3 RightFour11.region3 state group)
 (gone : endGroup group outcomes=[]) :
 6≤energy state final group outcomes := by
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
 obtain ⟨cut⟩ := first_any RightFour11.closed3 RightFour11.unique3 (by decide +kernel)
   logged valid.1 unique inside good reached.holes_sublist.subset gone
 obtain ⟨i,heroBefore,locksBefore⟩ := quiet_good_any RightFour11.closed3 RightFour11.unique3 cut.before
   valid.1 unique inside good reached.holes_sublist.subset
 have beforeLocks : [191,193,217]⊆endGroup group cut.beforeOutcomes := locksBefore
 have beforeReached := reached.append cut.before.logged.trace
 have beforeValid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant beforeReached
 have beforeFacts := cut.before.logged.end_subset valid.1 group unique inside
 have afterFacts := next_facts cut reached unique inside bounded
 have afterReached := beforeReached.append (Trace.cons cut.headChecked (Trace.nil cut.actor.state))
 have afterGone := tail_gone cut gone
 obtain ⟨source,owner,metadata,pays⟩ := cut.headPaid
 have exit : CutActor11.Exit source cut.direction := by
   rcases pays with ⟨rfl|rfl,h⟩ <;> simp [CutActor11.Exit,h]
 have row := CutStrict11.exit_row scalar rfl beforeValid cut.headChecked cut.headEffect beforeFacts.1 beforeFacts.2
   ⟨source,owner,metadata,exit⟩
 change 2≤charge NetHack.Soko11Hero315.holeWeight (endGroup group cut.beforeOutcomes) cut.headOutcome+
   value cut.actor.state (next cut)-value cut.middle (endGroup group cut.beforeOutcomes) at row
 have sum := two_tail cut reached unique inside bounded row
 rcases pays with ⟨rfl|rfl,directionEq⟩
 · have checked : step soko1_1.board cut.middle .east=some cut.actor := by simpa only [directionEq] using cut.headChecked
   have headEq := UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
     (show pushTargets soko1_1.board 191 .east=[192] by decide +kernel) (by decide +kernel) beforeReached.holes_sublist.subset
   have selected := update_mono [191,193,217] (endGroup group cut.beforeOutcomes) (by decide) beforeLocks cut.headOutcome
   have pair : [192,193]⊆next cut := by
     have small : [192,193]⊆update [191,193,217] (.push 191 (.stay 192)) := by decide
     rw [headEq] at selected
     change _ ⊆ update (endGroup group cut.beforeOutcomes) cut.headOutcome
     rw [headEq]
     exact List.Subset.trans small selected
   have physical : [192,193]⊆cut.actor.state.boulders := List.Subset.trans pair afterFacts.2.1
   exact False.elim (frozen_absurd cut.after (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant afterReached).1
     afterFacts.1 afterFacts.2.1 (Owner1007.locked_of_check _ [192,193] (by decide +kernel)) physical
     (show 192∈[192,193] by decide) (pair (by decide)) afterGone)
 · have checked : step soko1_1.board cut.middle .east=some cut.actor := by simpa only [directionEq] using cut.headChecked
   have headEq := UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
     (show pushTargets soko1_1.board 217 .east=[218] by decide +kernel) (by decide +kernel) beforeReached.holes_sublist.subset
   have effect : Matches cut.middle cut.actor (.push 217 (.stay 218)) := by simpa only [headEq] using cut.headEffect
   have selected := update_mono [191,193,217] (endGroup group cut.beforeOutcomes) (by decide) beforeLocks cut.headOutcome
   have triple : [191,193,218]⊆next cut := by
     have small : [191,193,218]⊆update [191,193,217] (.push 217 (.stay 218)) := by decide
     rw [headEq] at selected
     change _ ⊆ update (endGroup group cut.beforeOutcomes) cut.headOutcome
     rw [headEq]
     exact List.Subset.trans small selected
   have hero : cut.actor.state.player=217 := by rw [effect.2]
   have nextGood : OwnedCorral11.Good locks1 region1 cut.actor.state (next cut) := by
     refine ⟨0,?_,triple⟩
     rw [hero]; decide +kernel
   have tail := future_four afterReached cut.after (next cut) afterFacts.1 afterFacts.2.1 afterFacts.2.2 nextGood afterGone
   omega
#print axioms future_six


theorem debts_eight : U6.all (fun cell=>decide (cell∈C ∨ value soko1_1.initial [cell]≤-8))=true := by decide +kernel

theorem all_gone_eight {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : energy soko1_1.initial final U6 outcomes<8) :
 endGroup U6 outcomes=[] := by
 have dead : ∀ cell∈U6, endGroup [cell] outcomes=[] := by
   intro cell member
   apply Classical.byContradiction
   intro survives
   have sub : [cell]⊆U6 := by
     intro c found
     have same : c=cell:=List.mem_singleton.mp found
     exact same ▸ member
   have bound := energy_subset (Trace.nil soko1_1.initial) logged [cell] U6 (by simp) (by decide) sub (by decide) (by decide)
   have ledger := survivor_energy logged completed cell survives
   have row := of_decide_eq_true (List.all_eq_true.mp debts_eight cell member)
   have nn : (0:Int)≤Int.ofNat (ownPushes [cell] outcomes) := Int.ofNat_nonneg _
   rcases row with inC|debt
   · have ownCheap := UpperEightBudget11.cheap_others_six logged completed cheap cell inC
     have debt := of_decide_eq_true (List.all_eq_true.mp UpperCheapConsumed11.debts cell member)
     omega
   · omega
 have count := logged.end_count_le (by decide) U6 (by decide) (by decide) (fun _=>false)
   (by intro cell member _; exact dead cell member)
 have filterEmpty : ∀ xs : List Cell, xs.filter (fun _=>false)=[] := by
   intro xs
   induction xs with
   | nil => rfl
   | cons c rest ih => simpa only [List.filter,Bool.false_eq_true,if_false] using ih
 rw [filterEmpty] at count
 have zero : (endGroup U6 outcomes).length=0 := by simp only [List.length_nil] at count; omega
 exact List.eq_nil_of_length_eq_zero zero

theorem reserve_eight {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final)
 (cut : FirstCut UpperZero11.paid soko1_1.initial originalGroup dirs final pushes moves outcomes)
 (sourceEq : cut.actor.pushSource=some 216)
 (headEq : cut.headOutcome=.push 216 (.stay 217)) :
 8≤energy soko1_1.initial final U6 outcomes := by
 by_cases enough : 8≤energy soko1_1.initial final U6 outcomes
 · exact enough
 · have cheap : energy soko1_1.initial final U6 outcomes<8 := by omega
   have effect : Matches cut.middle cut.actor (.push 216 (.stay 217)) := by
     simpa only [headEq] using cut.headEffect
   obtain ⟨selected,_⟩ := Upper216After11.FirstCut.after_216east cut sourceEq effect
   have before191 : 191∈endGroup originalGroup cut.beforeOutcomes := by
     have found := selected (show 191∈([191,217] : List Cell) by simp)
     rw [headEq] at found
     simp only [update,move,post] at found
     split at found
     · exact List.mem_of_mem_erase (List.mem_cons.mp found |>.resolve_left (by decide))
     · exact found
   have stationary := cut.before.stationary UpperZero11.closed (by decide) (by decide) (by decide) (by decide)
     original_good (by simp) 191 (by simp) before191
   have prefixCheap := UpperEightBudget11.prefix_six logged completed cut cheap 193 (by decide)
   have guarded := StationaryGuardsSix11.guard193 cut.before.logged stationary prefixCheap
   have beforeGuard := cut.before.logged.end_subset (by decide) [193] (by decide) (by decide)
   have beforeValid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant cut.before.logged.trace
   have afterActual := step_boulders_nodup _ _ _ _ beforeValid.1 cut.headChecked
   have afterReached := cut.before.logged.trace.append (Trace.cons cut.headChecked (Trace.nil cut.actor.state))
   have upperBefore := cut.before.logged.end_subset (by decide) originalGroup (by decide) (by decide)
   have upperAfterInside := GhostSubset.update_subset _ _ _ cut.headEffect _ upperBefore.1 upperBefore.2
   have upperBeforeSubset := end_subset_selected cut.before.logged (by decide) originalGroup U6
     (by decide) (by decide) (by decide) (by decide)
   have upperAfterSubset := update_mono _ _ upperBefore.1 upperBeforeSubset cut.headOutcome
   have pair : [191,217]⊆UpperCutBudget11.nextGroup cut := List.Subset.trans selected upperAfterSubset
   have facts := UpperCutBudget11.next_facts cut
   have wholeGone := all_gone_eight logged completed cheap
   have gone : endGroup (UpperCutBudget11.nextGroup cut) cut.afterOutcomes=[] := by
     rw [cut.outcomesEq,endGroup_append] at wholeGone
     exact wholeGone
   have guardedSubset := end_subset_selected cut.before.logged (by decide) [193] U6
     (by decide) (by decide) (by decide) (by decide)
   have guardedNext := update_mono (endGroup [193] cut.beforeOutcomes) (endGroup U6 cut.beforeOutcomes) beforeGuard.1 guardedSubset cut.headOutcome
   have hero : cut.actor.state.player=216 := by rw [effect.2]
   rcases guarded with normal | shifted
   · have own193 : 193∈UpperCutBudget11.nextGroup cut := by
       apply guardedNext
       rw [headEq,normal]
       decide
     have triple : [191,193,217]⊆UpperCutBudget11.nextGroup cut := by
       intro c h
       simp only [List.mem_cons,List.not_mem_nil,or_false] at h
       rcases h with rfl|rfl|rfl
       · exact pair (by decide)
       · exact own193
       · exact pair (by decide)
     have good : OwnedCorral11.Good RightFour11.locks3 RightFour11.region3 cut.actor.state (UpperCutBudget11.nextGroup cut) := by
       refine ⟨0,?_,triple⟩
       rw [hero]; decide +kernel
     have future := future_six afterReached cut.after (UpperCutBudget11.nextGroup cut) facts.1 facts.2.1 facts.2.2 good gone
     have sum := UpperSixBudget11.two_tail_le cut
     omega
   · have physical192 : 192∈cut.actor.state.boulders := by
       have before : 192∈cut.middle.boulders := beforeGuard.2 (by rw [shifted]; simp)
       rw [effect.2]
       exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne (by decide : 192≠216)).mpr before)
     have physical : [191,192]⊆cut.actor.state.boulders := by
       intro c h
       rcases List.mem_cons.mp h with rfl|last
       · exact facts.2.1 (pair (by decide))
       · have same : c=192:=List.mem_singleton.mp last
         subst c
         exact physical192
     exact False.elim (frozen_absurd cut.after afterActual facts.1 facts.2.1
       (Owner1007.locked_of_check _ [191,192] (by decide +kernel)) physical
       (show 191∈[191,192] by decide) (pair (by decide)) gone)
#print axioms reserve_eight

end Owner1007.Upper216Eight11

