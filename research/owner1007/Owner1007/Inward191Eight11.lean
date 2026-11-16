import Owner1007.Gate191216Eight11
import Owner1007.Upper216Eight11
import Owner1007.QuietFixed11
namespace Owner1007.Inward191Eight11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11 Owner1007.UpperBudget11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def upper : List Cell:=PostCuts11.H.filter fun c=>decide (c<183∨c%26=24)
def locks (i : Fin 4) : List Cell:=match i.val with
 |0=>[138,139,191]
 |1=>[137,138,191]
 |2=>[164,191]
 |_=>[190,191]
def region (i : Fin 4) : List Cell:=match i.val with
 |0=>PostCuts11.without upper [138,139,164]
 |1=>PostCuts11.without upper [137,138,164]
 |2=>PostCuts11.without upper [164]
 |_=>upper
def paid (source : Cell) (dir : Dir) : Prop:=source=191∨(source=190∧dir=.south)
instance (c : Cell) (d : Dir) : Decidable (paid c d):=by unfold paid;infer_instance
theorem node0 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 0=true:=by decide +kernel
theorem node1 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 1=true:=by decide +kernel
theorem node2 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 2=true:=by decide +kernel
theorem node3 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 3=true:=by decide +kernel
theorem floor (i : Fin 4) : region i⊆soko1_1.board.floor:=by
 have row : (List.finRange 4).all (fun i=>(region i).all (fun c=>decide (c∈soko1_1.board.floor)))=true:=by decide +kernel
 intro c h
 exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp row i (by simp)) c h)
theorem unique : ∀i,(locks i).Nodup:=by decide +kernel
theorem nonempty : ∀i,locks i≠[]:=by decide +kernel
theorem has191 : ∀i,191∈locks i:=by decide +kernel
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid:=by
 apply FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked floor
 intro i
 obtain ⟨i,bound⟩:=i
 have cases : i=0∨i=1∨i=2∨i=3:=by omega
 rcases cases with rfl|rfl|rfl|rfl
 ·exact node0
 ·exact node1
 ·exact node2
 ·exact node3
def headCheck (i : Fin 4) : Bool:=([190,191]:List Cell).all fun source=>allDirs.all fun dir=>
 match advance soko1_1.board source dir.opposite with
 |none=>true
 |some hero=>decide (hero∈region i→¬BlockedPush soko1_1.board (locks i) source dir→
   paid source dir→source=190∧dir=.south)
theorem heads : ∀i,headCheck i=true:=by decide +kernel
theorem head_shape {state : State} {dir : Dir} {t : Transition} {source : Cell}
 (i : Fin 4) (hero : state.player∈region i) (physical : locks i⊆state.boulders)
 (pays : paid source dir) (checked : step soko1_1.board state dir=some t)
 (metadata : t.pushSource=some source) : source=190∧dir=.south:=by
 have member : source∈([190,191]:List Cell):=by rcases pays with rfl|⟨rfl,_⟩ <;> simp
 have row:=List.all_eq_true.mp (List.all_eq_true.mp (heads i) source member) dir (Geometry.all_directions dir)
 have adjacent:=PairPost11.source_adjacent checked metadata
 have behind:=Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked state.player (floor i hero) dir source adjacent
 simp only [headCheck,behind] at row
 exact of_decide_eq_true row hero (WestRankHead11.source_unblocked checked metadata physical) pays

theorem reserve_eight {state final : State}
 {beforeDirs dirs : List Dir} {beforePushes beforeMoves pushes moves : Nat} {before outcomes : List Outcome}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (last : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (stationary191 : ownPushes [191] before=0)
 (good : OwnedCorral11.Good locks region state (endGroup U6 before)) :
 8≤energy soko1_1.initial final U6 (before++outcomes):=by
 let logged:=first.append last
 by_cases enough : 8≤energy soko1_1.initial final U6 (before++outcomes)
 ·exact enough
 ·have cheap : energy soko1_1.initial final U6 (before++outcomes)<8:=by omega
  have valid:=NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace
  have facts:=first.end_subset (by decide) U6 (by decide) (by decide)
  have wholeGone:=Upper216Eight11.all_gone_eight logged completed cheap
  have gone : endGroup (endGroup U6 before) outcomes=[]:=by rw [←endGroup_append];exact wholeGone
  obtain ⟨cut⟩:=Upper216Eight11.first_any closed unique nonempty last valid.1 facts.1 facts.2 good first.trace.holes_sublist.subset gone
  obtain ⟨i,heroBefore,locksBefore⟩:=Upper216Eight11.quiet_good_any closed unique cut.before valid.1 facts.1 facts.2 good first.trace.holes_sublist.subset
  have beforeFacts:=cut.before.logged.end_subset valid.1 (endGroup U6 before) facts.1 facts.2
  have physicalBefore:=List.Subset.trans locksBefore beforeFacts.2
  obtain ⟨source,owner,metadata,pays⟩:=cut.headPaid
  obtain ⟨rfl,south⟩:=head_shape i heroBefore physicalBefore pays cut.headChecked metadata
  have checked : step soko1_1.board cut.middle .south=some cut.actor:=by simpa only [south] using cut.headChecked
  have currentFirst:=first.append cut.before.logged
  have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
    (show pushTargets soko1_1.board 190 .south=[216] by decide +kernel) (by decide +kernel) currentFirst.trace.holes_sublist.subset
  have effect : Matches cut.middle cut.actor (.push 190 (.stay 216)):=by simpa only [headEq] using cut.headEffect
  have initialOwn191 : 191∈endGroup U6 before:=by
    obtain ⟨j,_,sub⟩:=good
    exact sub (has191 j)
  have localZero:=cut.before.fixed initialOwn191 (by intro d;exact Or.inl rfl)
  have tag191:=no_push_unchanged [191] before stationary191
  have currentZero : ownPushes [191] (before++cut.beforeOutcomes)=0:=by
    rw [ownPushes_append,tag191,stationary191,localZero]
  let headLogged : Logged soko1_1.board cut.middle [.south] cut.actor.state cut.actor.pushCost 1 [.push 190 (.stay 216)]:=
    .cons checked effect (.nil _)
  let extended:=currentFirst.append headLogged
  have extendedZero : ownPushes [191] ((before++cut.beforeOutcomes)++[.push 190 (.stay 216)])=0:=by
    rw [ownPushes_append,no_push_unchanged _ _ currentZero]
    simpa [ownPushes,ownPush] using currentZero
  have owned : 216∈endGroup U6 ((before++cut.beforeOutcomes)++[.push 190 (.stay 216)]):=by
    rw [endGroup_append,endGroup_append]
    change 216∈update (endGroup (endGroup U6 before) cut.beforeOutcomes) (.push 190 (.stay 216))
    simp only [update,move,if_pos owner,post,List.mem_cons]
    exact Or.inl trivial
  have hero : cut.actor.state.player∈Gate191216Eight11.region 0:=by
    have same : cut.actor.state.player=190:=by rw [effect.2]
    rw [same]
    exact Gate191216Eight11.hero190
  have bound:=Gate191216Eight11.reserve_eight extended cut.after completed extendedZero owned hero
  have allEffects : ((before++cut.beforeOutcomes)++[.push 190 (.stay 216)])++cut.afterOutcomes=before++outcomes:=by
    calc
      _=(before++cut.beforeOutcomes)++.push 190 (.stay 216)::cut.afterOutcomes:=by simp only [List.append_assoc,List.singleton_append]
      _=before++(cut.beforeOutcomes++cut.headOutcome::cut.afterOutcomes):=by rw [headEq];simp only [List.append_assoc]
      _=before++outcomes:=congrArg (List.append before) cut.outcomesEq.symm
  rw [allEffects] at bound
  omega
#print axioms reserve_eight
end Owner1007.Inward191Eight11

