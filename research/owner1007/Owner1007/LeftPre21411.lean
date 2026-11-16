import Owner1007.LeftPre21411Data
import Owner1007.Post214LeftTwo11
import Owner1007.QuietGroupFixed11
import Owner1007.TransportQuiet11
namespace Owner1007.LeftPre21411
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem complete (i : Fin 4) (group : List Cell) (bounded : group.length≤4)
 (retained : locks i⊆group) (source : Cell) (owner : source∈group) : source∈locks i := by
 by_cases member : source∈locks i
 ·exact member
 ·have all : source::locks i⊆group:=List.cons_subset.mpr ⟨owner,retained⟩
  have card:=List.Nodup.length_le_of_subset (List.nodup_cons.mpr ⟨member,unique i⟩) all
  simp only [List.length_cons,size i] at card
  omega

theorem head_shape {state : State} {dir : Dir} {t : Transition} {source : Cell}
 (i : Fin 4) (hero : state.player∈region i) (physical : locks i⊆state.boulders)
 (sourceLock : source∈locks i) (pays : paid source dir)
 (checked : step soko1_1.board state dir=some t) (metadata : t.pushSource=some source) : Allowed source dir := by
 have r:=List.all_eq_true.mp (List.all_eq_true.mp (heads i) source sourceLock) dir (Geometry.all_directions dir)
 have adjacent:=PairPost11.source_adjacent checked metadata
 have behind:=Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked state.player (floor i hero) dir source adjacent
 simp only [headCheck,behind] at r
 exact of_decide_eq_true r hero (WestRankHead11.source_unblocked checked metadata physical) pays

theorem first_exit {state final history dirs past pastMoves pushes moves outcomes}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (i : Fin 4) (physical : locks i⊆state.boulders) (hero : state.player∈region i)
 (gone : endGroup (selected i) outcomes=[]) :
 ∃cut : FirstCut paid state (selected i) dirs final pushes moves outcomes,
 cut.actor.pushSource=some 213∧cut.direction=.east := by
 have actual:=(NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached).1
 have groupInside : selected i⊆state.boulders:=fun _ h=>physical ((selected_perm i).mem_iff.mp h)
 have good : OwnedCorral11.Good locks region state (selected i):=⟨i,hero,fun _ h=>(selected_perm i).mem_iff.mpr h⟩
 obtain ⟨cut⟩:=Upper216Eight11.first_any closed unique nonempty logged actual (selected_unique i) groupInside good reached.holes_sublist.subset gone
 obtain ⟨j,heroBefore,retained⟩:=Upper216Eight11.quiet_good_any closed unique cut.before actual (selected_unique i) groupInside good reached.holes_sublist.subset
 have beforeFacts:=cut.before.logged.end_subset actual (selected i) (selected_unique i) groupInside
 have beforeReached:=reached.append cut.before.logged.trace
 have nextReached:=beforeReached.append (Trace.cons cut.headChecked (Trace.nil cut.actor.state))
 have bound : (selected i).length≤18:=by change 4≤18;decide
 have nextFacts:=Upper216Eight11.next_facts cut reached (selected_unique i) groupInside bound
 obtain ⟨source,owner,metadata,pays⟩:=cut.headPaid
 have currentBound : (endGroup (selected i) cut.beforeOutcomes).length≤4:=endGroup_length_le (selected i) cut.beforeOutcomes
 have sourceLock:=complete j _ currentBound retained source owner
 have allowed:=head_shape j heroBefore (List.Subset.trans retained beforeFacts.2) sourceLock pays cut.headChecked metadata
 have dead {landing : Cell} (targets : pushTargets soko1_1.board source cut.direction=[landing])
  (unfilled : landing∉soko1_1.initial.holes) (frozen : List Cell) (locked : Locked soko1_1.board frozen)
  (shift : frozen⊆landing::(locks j).erase source) (member : landing∈frozen) : False := by
  have shape:=UpperHeadCases11.ordinary_effect cut.headChecked cut.headEffect metadata targets unfilled beforeReached.holes_sublist.subset
  have kept:=CageFour12.shifted_inside (unique j) retained owner shift
  have current : frozen⊆Upper216Eight11.next cut:=by simpa only [Upper216Eight11.next,shape] using kept
  have owns : landing∈Upper216Eight11.next cut:=by
   change landing∈update (endGroup (selected i) cut.beforeOutcomes) cut.headOutcome
   rw [shape];simp [update,move,owner,post]
  exact Upper216Eight11.frozen_absurd cut.after (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant nextReached).1
    nextFacts.1 nextFacts.2.1 locked (List.Subset.trans current nextFacts.2.1) member owns (Upper216Eight11.tail_gone cut gone)
 rcases allowed with ⟨rfl,west⟩|⟨rfl,east⟩|⟨rfl,east⟩|⟨rfl,east⟩
 ·have shift:∀j:Fin 4,[183]⊆183::(locks j).erase 184:=by decide +kernel
  exact False.elim (dead (by rw [west];decide +kernel) (by decide +kernel) [183] Post214LeftTwo11.frozen183 (shift j) (by simp))
 ·have shift:∀j:Fin 4,[186,187]⊆186::(locks j).erase 185:=by decide +kernel
  exact False.elim (dead (by rw [east];decide +kernel) (by decide +kernel) [186,187] Post214LeftTwo11.frozen186187 (shift j) (by simp))
 ·have shift:∀j:Fin 4,[188,189]⊆188::(locks j).erase 187:=by decide +kernel
  exact False.elim (dead (by rw [east];decide +kernel) (by decide +kernel) [188,189] Post214LeftTwo11.frozen188189 (shift j) (by simp))
 ·exact ⟨cut,metadata,east⟩

def postIndex (i : Fin 4) : Fin 2:=if i.val%2=0 then 0 else 1

theorem future_four {state final history dirs past pastMoves pushes moves outcomes}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (i : Fin 4) (physical : locks i⊆state.boulders) (hero : state.player∈region i)
 (gone : endGroup (selected i) outcomes=[]) :
 4≤energy state final (pair i) outcomes := by
 have valid:=NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
 have groupInside : selected i⊆state.boulders:=fun _ h=>physical ((selected_perm i).mem_iff.mp h)
 have pairInside : pair i⊆state.boulders:=List.Subset.trans (pair_selected i) groupInside
 have upperInside : [187,189]⊆state.boulders:=List.Subset.trans (List.subset_append_right _ _) groupInside
 have good : OwnedCorral11.Good locks region state (selected i):=⟨i,hero,fun _ h=>(selected_perm i).mem_iff.mpr h⟩
 obtain ⟨cut,metadata,east⟩:=first_exit reached logged i physical hero gone
 obtain ⟨j,heroBefore,retained⟩:=Upper216Eight11.quiet_good_any closed unique cut.before valid.1 (selected_unique i) groupInside good reached.holes_sublist.subset
 have beforeFacts:=cut.before.logged.end_subset valid.1 (selected i) (selected_unique i) groupInside
 have currentBound : (endGroup (selected i) cut.beforeOutcomes).length≤4:=endGroup_length_le (selected i) cut.beforeOutcomes
 have wholePerm : (endGroup (selected i) cut.beforeOutcomes).Perm (selected j) := by
  have toLocks : (endGroup (selected i) cut.beforeOutcomes).Perm (locks j):=
   (List.perm_ext_iff_of_nodup beforeFacts.1 (unique j)).mpr (fun c=>⟨complete j _ currentBound retained c,(fun h=>retained h)⟩)
  exact toLocks.trans (selected_perm j).symm
 have upperQuiet:=TransportQuiet11.Quiet.project cut.before valid.1 (selected_unique i) groupInside [187,189] (by decide) (List.subset_append_right _ _)
 have upperFixed:=no_push_unchanged [187,189] cut.beforeOutcomes (QuietGroupFixed11.whole_fixed upperQuiet (by
   intro c member dir
   simp only [List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl <;>simp [paid]))
 have split:=cut.before.logged.end_split valid.1 (pair i) [187,189] (selected_unique i) groupInside
 rw [upperFixed] at split
 have pairPerm : (endGroup (pair i) cut.beforeOutcomes).Perm (pair j):=
  (List.perm_append_right_iff [187,189]).mp (split.trans wholePerm)
 have pairFacts:=cut.before.logged.end_subset valid.1 (pair i) (pair_unique i) pairInside
 have beforeReached:=reached.append cut.before.logged.trace
 have beforeValid:=NetHack.SokobanLinearPhases.Map11.trace_phase_invariant beforeReached
 have checked : step soko1_1.board cut.middle .east=some cut.actor:=by simpa only [east] using cut.headChecked
 have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
   (show pushTargets soko1_1.board 213 .east=[214] by decide +kernel) (by decide +kernel) beforeReached.holes_sublist.subset
 have effect : Matches cut.middle cut.actor (.push 213 (.stay 214)):=by simpa only [headEq] using cut.headEffect
 obtain ⟨source,owner,sourceEq,pays⟩:=cut.headPaid
 have source213 : source=213:=Option.some.inj (sourceEq.symm.trans metadata)
 have sourceLock:=complete j _ currentBound retained source owner
 have front213 : front j=213:=by
  have row:∀j:Fin 4,(213:Cell)∈locks j→front j=213:=by decide +kernel
  exact row j (source213 ▸ sourceLock)
 have leftOwn : 213∈endGroup (pair i) cut.beforeOutcomes:=pairPerm.mem_iff.mpr (by simp [pair,front213])
 have row:=UpperLocalPrice11.exit_row beforeValid pairFacts.1 pairFacts.2 cut.headChecked cut.headEffect
   ⟨213,leftOwn,metadata,by simp [UpperLocalPrice11.paid,UpperLocalPrice11.eastSources,east]⟩
 change 2≤charge NetHack.Soko11Hero315.holeWeight (endGroup (pair i) cut.beforeOutcomes) cut.headOutcome+
   value cut.actor.state (update (endGroup (pair i) cut.beforeOutcomes) cut.headOutcome)-value cut.middle (endGroup (pair i) cut.beforeOutcomes) at row
 have afterGroup := update_perm wholePerm cut.headOutcome
 have groupShift : ∀j:Fin 4,front j=213→(update (selected j) (.push 213 (.stay 214))).Perm (Post214LeftTwo11.selected (postIndex j)):=by decide +kernel
 have pairShift : ∀j:Fin 4,front j=213→(update (pair j) (.push 213 (.stay 214))).Perm (Post214LeftTwo11.left (postIndex j)):=by decide +kernel
 have afterPerm : (Upper216Eight11.next cut).Perm (Post214LeftTwo11.selected (postIndex j)):=by
  change (update (endGroup (selected i) cut.beforeOutcomes) cut.headOutcome).Perm _
  rw [headEq] at afterGroup ⊢
  exact afterGroup.trans (groupShift j front213)
 have afterPair : (update (endGroup (pair i) cut.beforeOutcomes) cut.headOutcome).Perm (Post214LeftTwo11.left (postIndex j)):=by
  rw [headEq]
  exact (update_perm pairPerm _).trans (pairShift j front213)
 have bound : (selected i).length≤18:=by change 4≤18;decide
 have afterFacts:=Upper216Eight11.next_facts cut reached (selected_unique i) groupInside bound
 have nextReached:=beforeReached.append (Trace.cons cut.headChecked (Trace.nil cut.actor.state))
 have postPhysical : Post214LeftTwo11.locks (postIndex j)⊆cut.actor.state.boulders:=by
  intro c member
  exact afterFacts.2.1 (afterPerm.mem_iff.mpr ((Post214LeftTwo11.selected_perm _).mem_iff.mpr member))
 have postHero : cut.actor.state.player∈Post214LeftTwo11.region (postIndex j):=by
  rw [effect.2]
  have row:∀j:Fin 4,(213:Cell)∈Post214LeftTwo11.region (postIndex j):=by decide +kernel
  exact row j
 have tail:=Post214LeftTwo11.future_two_perm nextReached cut.after (postIndex j) postPhysical postHero
   (Upper216Eight11.next cut) (update (endGroup (pair i) cut.beforeOutcomes) cut.headOutcome) afterPerm afterPair
   (Upper216Eight11.tail_gone cut gone)
 have prefixNN:=HeroLedger.Logged.energy_nonnegative cut.before.logged (groupCertificate 18) valid (pair i) (pair_unique i) pairInside (by change 2≤18;decide)
 change 0≤energy state cut.middle (pair i) cut.beforeOutcomes at prefixNN
 have splitEnergy:=energy_append state cut.middle final (pair i) cut.beforeOutcomes (cut.headOutcome::cut.afterOutcomes)
 have one:=OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight cut.middle cut.actor.state final
   (endGroup (pair i) cut.beforeOutcomes) cut.headOutcome cut.afterOutcomes
 change energy cut.middle final (endGroup (pair i) cut.beforeOutcomes) (cut.headOutcome::cut.afterOutcomes)=
   charge NetHack.Soko11Hero315.holeWeight (endGroup (pair i) cut.beforeOutcomes) cut.headOutcome+
   value cut.actor.state (update (endGroup (pair i) cut.beforeOutcomes) cut.headOutcome)-value cut.middle (endGroup (pair i) cut.beforeOutcomes)+
   energy cut.actor.state final (update (endGroup (pair i) cut.beforeOutcomes) cut.headOutcome) cut.afterOutcomes at one
 have same:=congrArg (energy state final (pair i)) cut.outcomesEq
 omega
#print axioms first_exit
#print axioms future_four
end Owner1007.LeftPre21411
