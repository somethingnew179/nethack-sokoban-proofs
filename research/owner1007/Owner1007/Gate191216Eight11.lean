import Owner1007.Later216Eight11
import Owner1007.WestRankHead11
import Owner1007.QuietFixed11
namespace Owner1007.Gate191216Eight11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11 Owner1007.UpperBudget11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def locks (_ : Fin 1) : List Cell:=[191,216]
def region (_ : Fin 1) : List Cell:=PostCuts11.without PostCuts11.H [191,192,193,194,216,217,218,219,220]
def paid (source : Cell) (_ : Dir) : Prop:=source=191∨source=216
instance (c : Cell) (d : Dir) : Decidable (paid c d):=by unfold paid;infer_instance
theorem matrix : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 0=true:=by decide +kernel
theorem floor (i : Fin 1) : region i⊆soko1_1.board.floor:=by
 have row : (region 0).all (fun c=>decide (c∈soko1_1.board.floor))=true:=by decide +kernel
 intro c h
 exact of_decide_eq_true (List.all_eq_true.mp row c h)
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid:=by
 apply FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked floor
 intro i
 have same : i=0:=Fin.ext (by omega)
 simpa only [same] using matrix
def headCheck : Bool:=([191,216]:List Cell).all fun source=>allDirs.all fun dir=>
 match advance soko1_1.board source dir.opposite with
 |none=>true
 |some hero=>decide (hero∉region 0 ∨BlockedPush soko1_1.board (locks 0) source dir ∨dir=.east)
theorem head_checked : headCheck=true:=by decide +kernel
theorem head_east {state : State} {dir : Dir} {t : Transition} {source : Cell}
 (hero : state.player∈region 0) (inside : locks 0⊆state.boulders)
 (member : source∈locks 0) (checked : step soko1_1.board state dir=some t)
 (metadata : t.pushSource=some source) : dir=.east:=by
 have adjacent:=PairPost11.source_adjacent checked metadata
 have behind:=Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked state.player (floor 0 hero) dir source adjacent
 have row:=List.all_eq_true.mp (List.all_eq_true.mp head_checked source member) dir (Geometry.all_directions dir)
 simp only [headCheck,behind] at row
 exact ((of_decide_eq_true row).resolve_left (fun h=>h hero)).resolve_left
   (WestRankHead11.source_unblocked checked metadata inside)

theorem reserve_eight {state final : State}
 {beforeDirs dirs : List Dir} {beforePushes beforeMoves pushes moves : Nat} {before outcomes : List Outcome}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (last : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (stationary191 : ownPushes [191] before=0)
 (owns216 : 216∈endGroup U6 before) (hero : state.player∈region 0) :
 8≤energy soko1_1.initial final U6 (before++outcomes):=by
 let logged:=first.append last
 by_cases enough : 8≤energy soko1_1.initial final U6 (before++outcomes)
 ·exact enough
 ·have cheap : energy soko1_1.initial final U6 (before++outcomes)<8:=by omega
  have valid:=NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace
  have facts:=first.end_subset (by decide) U6 (by decide) (by decide)
  have tag191:=no_push_unchanged [191] before stationary191
  have singleSubset:=first.end_mono (by decide) [191] U6 (by decide) (by decide) (by decide)
  have owns191 : 191∈endGroup U6 before:=singleSubset (by rw [tag191];simp)
  have physical : locks 0⊆endGroup U6 before:=by
    intro c h
    rcases List.mem_cons.mp h with rfl|later
    ·exact owns191
    ·have same : c=216:=List.mem_singleton.mp later
     subst c;exact owns216
  have good : OwnedCorral11.Good locks region state (endGroup U6 before):=⟨0,hero,physical⟩
  have wholeGone:=Upper216Eight11.all_gone_eight logged completed cheap
  have gone : endGroup (endGroup U6 before) outcomes=[]:=by rw [←endGroup_append];exact wholeGone
  obtain ⟨cut⟩:=Upper216Eight11.first_any closed (by decide +kernel) (by decide +kernel)
    last valid.1 facts.1 facts.2 good first.trace.holes_sublist.subset gone
  obtain ⟨i,heroBefore,locksBefore⟩:=Upper216Eight11.quiet_good_any closed (by decide +kernel) cut.before
    valid.1 facts.1 facts.2 good first.trace.holes_sublist.subset
  have beforeFacts:=cut.before.logged.end_subset valid.1 (endGroup U6 before) facts.1 facts.2
  have physicalBefore : locks 0⊆cut.middle.boulders:=List.Subset.trans locksBefore beforeFacts.2
  have currentFirst:=first.append cut.before.logged
  have localZero191:=cut.before.fixed owns191 (by intro d;exact Or.inl rfl)
  have zero191 : ownPushes [191] (before++cut.beforeOutcomes)=0:=by
    rw [ownPushes_append,tag191,stationary191,localZero191]
  have allEffects : (before++cut.beforeOutcomes)++cut.headOutcome::cut.afterOutcomes=before++outcomes:=by
    calc
      _=before++(cut.beforeOutcomes++cut.headOutcome::cut.afterOutcomes):=by simp only [List.append_assoc]
      _=before++outcomes:=congrArg (List.append before) cut.outcomesEq.symm
  obtain ⟨source,owner,metadata,pays⟩:=cut.headPaid
  have member : source∈locks 0:=by rcases pays with rfl|rfl <;> decide
  have east:=head_east heroBefore physicalBefore member cut.headChecked metadata
  have checked : step soko1_1.board cut.middle .east=some cut.actor:=by simpa only [east] using cut.headChecked
  rcases pays with rfl|rfl
  ·have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
     (show pushTargets soko1_1.board 191 .east=[192] by decide +kernel) (by decide +kernel) currentFirst.trace.holes_sublist.subset
   have effect : Matches cut.middle cut.actor (.push 191 (.stay 192)):=by simpa only [headEq] using cut.headEffect
   have whole193:=UpperEightBudget11.cheap_others_six logged completed cheap 193 (by decide)
   have prefix193:=prefix_energy_le currentFirst (Logged.cons cut.headChecked cut.headEffect cut.after) [193] (by decide) (by decide)
   rw [allEffects] at prefix193
   have cheap193 : energy soko1_1.initial cut.middle [193] (before++cut.beforeOutcomes)<6:=by omega
   have survives:=StationaryExitSix11.survives191 currentFirst checked effect cut.after zero191 cheap193
   have eq:=allEffects
   rw [headEq] at eq
   have wholeSurvives : endGroup [191] (before++outcomes)≠[]:=by rw [←eq];exact survives
   exact False.elim (UpperEightExit11.survivor_eight_absurd logged completed cheap 191 (by simp) wholeSurvives)
  ·have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
     (show pushTargets soko1_1.board 216 .east=[217] by decide +kernel) (by decide +kernel) currentFirst.trace.holes_sublist.subset
   have effect : Matches cut.middle cut.actor (.push 216 (.stay 217)):=by simpa only [headEq] using cut.headEffect
   have owned : 216∈endGroup U6 (before++cut.beforeOutcomes):=by rw [endGroup_append];exact owner
   have later:=Later216Eight11.reserve_eight currentFirst checked effect cut.after completed zero191 owned
   have eq:=allEffects
   rw [headEq] at eq
   rw [eq] at later
   omega
theorem hero190 : (190:Cell)∈region 0:=by decide +kernel
#print axioms reserve_eight
end Owner1007.Gate191216Eight11

