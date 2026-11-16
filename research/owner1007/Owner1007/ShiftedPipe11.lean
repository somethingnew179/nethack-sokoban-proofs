import Owner1007.Upper189WestAt18611
import Owner1007.Upper216Eight11
import Owner1007.QuietFixed11
namespace Owner1007.ShiftedPipe11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
structure Certificate (n : Nat) where
 locks : Fin n→List Cell
 region : Fin n→List Cell
 u : Fin n→Cell
 paid : Cell→Dir→Prop
 terminal : Fin n→Bool
 unique : ∀i,(locks i).Nodup
 nonempty : ∀i,locks i≠[]
 size : ∀i,(locks i).length=4
 closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid
 u_mem : ∀i,u i∈locks i
 u_options : ∀i,u i=186∨u i=187
 only_u : ∀i c,(c=186∨c=187)→c∈locks i→c=u i
 u_paid : ∀i dir,paid (u i) dir
 right_mem : ∀i,(189:Cell)∈locks i
 right_paid : ∀dir,paid 189 dir
 frozen_shift : ∀i,u i=187→[187,188]⊆update (locks i) (.push 189 (.stay 188))
 head : ∀{state : State}{dir : Dir}{t : Transition}{source : Cell}(i : Fin n),
  state.player∈region i→source∈locks i→locks i⊆state.boulders→
  step soko1_1.board state dir=some t→t.pushSource=some source→paid source dir→
  terminal i=true∨(source=189∧dir=.west)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem canonical {n : Nat} (spec : Certificate n) (j : Fin n) (group : List Cell)
 (unique : group.Nodup) (bounded : group.length≤4) (inside : spec.locks j⊆group) :
 group.Perm (spec.locks j):=by
 apply (List.perm_ext_iff_of_nodup unique (spec.unique j)).mpr
 intro cell
 constructor
 ·intro member
  by_cases known : cell∈spec.locks j
  ·exact known
  ·have selected : cell::spec.locks j⊆group:=List.cons_subset.mpr ⟨member,inside⟩
   have card:=List.Nodup.length_le_of_subset (List.nodup_cons.mpr ⟨known,spec.unique j⟩) selected
   simp only [List.length_cons,spec.size] at card
   omega
 ·exact fun h=>inside h

theorem impossible {n : Nat} (spec : Certificate n)
 (dead : ∀{state final : State}{history dirs : List Dir}{past pastMoves pushes moves : Nat}{outcomes : List Outcome},
  Trace soko1_1.board soko1_1.initial history state past pastMoves→
  Logged soko1_1.board state dirs final pushes moves outcomes→
  ∀i : Fin n,spec.terminal i=true→spec.locks i⊆state.boulders→state.player∈spec.region i→
   endGroup (spec.locks i) outcomes=[]→False)
 {state final : State} {beforeDirs dirs : List Dir} {beforePushes beforeMoves pushes moves : Nat} {before outcomes : List Outcome}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (upperCap : energy soko1_1.initial final UpperBudget11.U6 (before++outcomes)≤6)
 (prefixPair : 2≤energy soko1_1.initial state TightSplit11.A before)
 (i : Fin n) (tag188 : endGroup [188] before=[spec.u i]) (tag191 : endGroup [191] before=[189])
 (inside : spec.locks i⊆state.boulders) (hero : state.player∈spec.region i)
 (gone : endGroup (spec.locks i) outcomes=[]) : False:=by
 have valid:=NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace
 have good : OwnedCorral11.Good spec.locks spec.region state (spec.locks i):=⟨i,hero,List.Subset.refl _⟩
 obtain ⟨cut⟩:=Upper216Eight11.first_any spec.closed spec.unique spec.nonempty logged valid.1 (spec.unique i) inside good first.trace.holes_sublist.subset gone
 obtain ⟨j,heroBefore,retained⟩:=Upper216Eight11.quiet_good_any spec.closed spec.unique cut.before valid.1 (spec.unique i) inside good first.trace.holes_sublist.subset
 have beforeFacts:=cut.before.logged.end_subset valid.1 (spec.locks i) (spec.unique i) inside
 have beforeBound : (endGroup (spec.locks i) cut.beforeOutcomes).length≤4:=by
  have bound:=endGroup_length_le (spec.locks i) cut.beforeOutcomes
  rw [spec.size] at bound
  exact bound
 have same:=canonical spec j _ beforeFacts.1 beforeBound retained
 let current:=first.append cut.before.logged
 let remaining : Logged soko1_1.board cut.middle (cut.direction::cut.afterDirs) final (cut.actor.pushCost+cut.afterPushes) (1+cut.afterMoves) (cut.headOutcome::cut.afterOutcomes):=
  .cons cut.headChecked cut.headEffect cut.after
 have beforeGone : endGroup (endGroup (spec.locks i) cut.beforeOutcomes) (cut.headOutcome::cut.afterOutcomes)=[]:=by
  have g:=gone
  rw [cut.outcomesEq,endGroup_append] at g
  exact g
 have exactGone : endGroup (spec.locks j) (cut.headOutcome::cut.afterOutcomes)=[]:=by
  have equivalent:=endGroup_perm same (cut.headOutcome::cut.afterOutcomes)
  rw [beforeGone] at equivalent
  exact List.perm_nil.mp equivalent.symm
 obtain ⟨source,owner,metadata,pays⟩:=cut.headPaid
 have member : source∈spec.locks j:=same.mem_iff.mp owner
 rcases spec.head j heroBefore member (List.Subset.trans retained beforeFacts.2) cut.headChecked metadata pays with terminal|⟨rfl,west⟩
 ·exact dead current.trace remaining j terminal (List.Subset.trans retained beforeFacts.2) heroBefore exactGone
 ·have checked : step soko1_1.board cut.middle .west=some cut.actor:=by simpa only [west] using cut.headChecked
  have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
   (show pushTargets soko1_1.board 189 .west=[188] by decide +kernel) (by decide +kernel) current.trace.holes_sublist.subset
  have effect : Matches cut.middle cut.actor (.push 189 (.stay 188)):=by simpa only [headEq] using cut.headEffect
  rcases spec.u_options j with is186|is187
  ·have fixedU:=no_push_unchanged [spec.u i] cut.beforeOutcomes (cut.before.fixed (spec.u_mem i) (spec.u_paid i))
   have nested:=cut.before.logged.end_mono valid.1 [spec.u i] (spec.locks i) (by simp)
    (by intro c h;have eq:=List.mem_singleton.mp h;subst c;exact inside (spec.u_mem i))
    (by simpa using spec.u_mem i)
   have uPresent : spec.u i∈endGroup (spec.locks i) cut.beforeOutcomes:=by
    rw [fixedU] at nested
    exact nested (by simp)
   have uEq:=spec.only_u j (spec.u i) (spec.u_options i) (same.mem_iff.mp uPresent)
   have current188 : endGroup [188] (before++cut.beforeOutcomes)=[186]:=by
    rw [endGroup_append,tag188,fixedU,uEq,is186]
   have fixedRight:=no_push_unchanged [189] cut.beforeOutcomes (cut.before.fixed (spec.right_mem i) spec.right_paid)
   have current191 : endGroup [191] (before++cut.beforeOutcomes)=[189]:=by rw [endGroup_append,tag191,fixedRight]
   have monoPair:=prefix_energy_le first cut.before.logged TightSplit11.A (by decide) (by decide)
   have currentPair : 2≤energy soko1_1.initial cut.middle TightSplit11.A (before++cut.beforeOutcomes):=by omega
   have eight:=Upper189WestAt18611.upper_eight current checked effect cut.after current188 current191 currentPair
   have sequence : (before++cut.beforeOutcomes)++.push 189 (.stay 188)::cut.afterOutcomes=before++outcomes:=by
    rw [←headEq,List.append_assoc,←cut.outcomesEq]
   rw [sequence] at eight
   omega
  ·have shifted:=spec.frozen_shift j is187
   have lifted:=update_mono (spec.locks j) (endGroup (spec.locks i) cut.beforeOutcomes) (spec.unique j) retained cut.headOutcome
   have pair : [187,188]⊆Upper216Eight11.next cut:=by
    change _⊆update (endGroup (spec.locks i) cut.beforeOutcomes) cut.headOutcome
    rw [headEq] at lifted ⊢
    exact List.Subset.trans shifted lifted
   have afterFacts:=Upper216Eight11.next_facts cut first.trace (spec.unique i) inside (by rw [spec.size];omega)
   have reached:=current.trace.append (Trace.cons cut.headChecked (Trace.nil cut.actor.state))
   exact Upper216Eight11.frozen_absurd cut.after (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached).1
    afterFacts.1 afterFacts.2.1 (locked_of_check _ [187,188] (by decide +kernel))
    (List.Subset.trans pair afterFacts.2.1) (show 187∈([187,188]:List Cell) by decide) (pair (show 187∈([187,188]:List Cell) by decide)) (Upper216Eight11.tail_gone cut gone)
#print axioms canonical
#print axioms impossible
end Owner1007.ShiftedPipe11
