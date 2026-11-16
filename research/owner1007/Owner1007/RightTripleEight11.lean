import Owner1007.Gate191216Eight11
namespace Owner1007.RightTripleEight11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11 Owner1007.UpperBudget11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def locks (_ : Fin 1) : List Cell:=[191,193,216]
def region (_ : Fin 1) : List Cell:=Gate191216Eight11.region 0
def paid (source : Cell) (dir : Dir) : Prop:=(source=191∨source=216)∧dir=.east
instance (c : Cell) (d : Dir) : Decidable (paid c d):=by unfold paid;infer_instance
theorem matrix : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 0=true:=by decide +kernel
theorem floor (i : Fin 1) : region i⊆soko1_1.board.floor:=Gate191216Eight11.floor 0
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid:=by
 apply FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked floor
 intro i
 have same : i=0:=Fin.ext (by omega)
 simpa only [same] using matrix

theorem future_eight {state final : State} {history dirs : List Dir} {past pastMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (group : List Cell) (unique : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤18)
 (hero : state.player∈region 0) (selected : locks 0⊆group) (gone : endGroup group outcomes=[]) :
 8≤energy state final group outcomes:=by
 have valid:=NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
 have good : OwnedCorral11.Good locks region state group:=⟨0,hero,selected⟩
 obtain ⟨cut⟩:=Upper216Eight11.first_any closed (by decide +kernel) (by decide +kernel)
   logged valid.1 unique inside good reached.holes_sublist.subset gone
 obtain ⟨i,heroBefore,locksBefore⟩:=Upper216Eight11.quiet_good_any closed (by decide +kernel) cut.before
   valid.1 unique inside good reached.holes_sublist.subset
 have beforeLocks : [191,193,216]⊆endGroup group cut.beforeOutcomes:=locksBefore
 have beforeFacts:=cut.before.logged.end_subset valid.1 group unique inside
 have beforeReached:=reached.append cut.before.logged.trace
 have beforeValid:=NetHack.SokobanLinearPhases.Map11.trace_phase_invariant beforeReached
 have nextFacts:=Upper216Eight11.next_facts cut reached unique inside bounded
 have nextReached:=beforeReached.append (Trace.cons cut.headChecked (Trace.nil cut.actor.state))
 have nextGone:=Upper216Eight11.tail_gone cut gone
 obtain ⟨source,owner,metadata,pays⟩:=cut.headPaid
 have exit : CutActor11.Exit source cut.direction:=by
   rcases pays with ⟨rfl|rfl,east⟩ <;> simp [CutActor11.Exit,east]
 have row:=CutStrict11.exit_row scalar rfl beforeValid cut.headChecked cut.headEffect beforeFacts.1 beforeFacts.2
   ⟨source,owner,metadata,exit⟩
 change 2≤charge NetHack.Soko11Hero315.holeWeight (endGroup group cut.beforeOutcomes) cut.headOutcome+
   value cut.actor.state (Upper216Eight11.next cut)-value cut.middle (endGroup group cut.beforeOutcomes) at row
 have sum:=Upper216Eight11.two_tail cut reached unique inside bounded row
 rcases pays with ⟨rfl|rfl,east⟩
 ·have checked : step soko1_1.board cut.middle .east=some cut.actor:=by simpa only [east] using cut.headChecked
  have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
    (show pushTargets soko1_1.board 191 .east=[192] by decide +kernel) (by decide +kernel) beforeReached.holes_sublist.subset
  have all:=update_mono [191,193,216] (endGroup group cut.beforeOutcomes) (by decide) beforeLocks cut.headOutcome
  have pair : [192,193]⊆Upper216Eight11.next cut:=by
    change [192,193]⊆update (endGroup group cut.beforeOutcomes) cut.headOutcome
    rw [headEq] at all ⊢
    exact List.Subset.trans (by decide) all
  have physical:=List.Subset.trans pair nextFacts.2.1
  exact False.elim (Upper216Eight11.frozen_absurd cut.after
    (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant nextReached).1 nextFacts.1 nextFacts.2.1
    (Owner1007.locked_of_check _ [192,193] (by decide +kernel)) physical (show 192∈[192,193] by decide)
    (pair (by decide)) nextGone)
 ·have checked : step soko1_1.board cut.middle .east=some cut.actor:=by simpa only [east] using cut.headChecked
  have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
    (show pushTargets soko1_1.board 216 .east=[217] by decide +kernel) (by decide +kernel) beforeReached.holes_sublist.subset
  have effect : Matches cut.middle cut.actor (.push 216 (.stay 217)):=by simpa only [headEq] using cut.headEffect
  have all:=update_mono [191,193,216] (endGroup group cut.beforeOutcomes) (by decide) beforeLocks cut.headOutcome
  have triple : [191,193,217]⊆Upper216Eight11.next cut:=by
    change [191,193,217]⊆update (endGroup group cut.beforeOutcomes) cut.headOutcome
    rw [headEq] at all ⊢
    exact List.Subset.trans (by decide) all
  have afterHero : cut.actor.state.player=216:=by rw [effect.2]
  have nextGood : OwnedCorral11.Good RightFour11.locks3 RightFour11.region3 cut.actor.state (Upper216Eight11.next cut):=by
    refine ⟨0,?_,triple⟩
    rw [afterHero];decide +kernel
  have future:=Upper216Eight11.future_six nextReached cut.after (Upper216Eight11.next cut)
    nextFacts.1 nextFacts.2.1 nextFacts.2.2 nextGood nextGone
  omega

theorem reserve_eight {state final : State}
 {beforeDirs dirs : List Dir} {beforePushes beforeMoves pushes moves : Nat} {before outcomes : List Outcome}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (last : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (hero : state.player∈region 0) (selected : locks 0⊆endGroup U6 before) :
 8≤energy soko1_1.initial final U6 (before++outcomes):=by
 let logged:=first.append last
 by_cases enough : 8≤energy soko1_1.initial final U6 (before++outcomes)
 ·exact enough
 ·have cheap : energy soko1_1.initial final U6 (before++outcomes)<8:=by omega
  have facts:=first.end_subset (by decide) U6 (by decide) (by decide)
  have gone:=Upper216Eight11.all_gone_eight logged completed cheap
  have suffixGone : endGroup (endGroup U6 before) outcomes=[]:=by rw [←endGroup_append];exact gone
  have bounded:=endGroup_length_le U6 before
  change (endGroup U6 before).length≤6 at bounded
  have tail:=future_eight first.trace last (endGroup U6 before) facts.1 facts.2 (by omega) hero selected suffixGone
  have prefixNN:=energy_nonnegative first U6 (by decide) (by decide)
  have append:=energy_append soko1_1.initial state final U6 before outcomes
  omega
#print axioms future_eight
#print axioms reserve_eight
end Owner1007.RightTripleEight11

