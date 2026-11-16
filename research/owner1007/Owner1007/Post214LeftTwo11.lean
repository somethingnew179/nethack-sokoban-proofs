import Owner1007.Post214LeftTwo11Data
import Owner1007.LeftGateReserve11
namespace Owner1007.Post214LeftTwo11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def left (i : Fin 2) : List Cell := if i.val=0 then [184,214] else [185,214]
def selected (i : Fin 2) : List Cell := left i++[187,189]
theorem selected_perm : ∀i,(selected i).Perm (locks i) := by decide +kernel

theorem first_exit {state final history dirs past pastMoves pushes moves outcomes}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (i : Fin 2) (physical : locks i⊆state.boulders) (hero : state.player∈region i)
 (gone : endGroup (selected i) outcomes=[]) :
 ∃cut : FirstCut paid state (selected i) dirs final pushes moves outcomes,
 (cut.actor.pushSource=some 185∧cut.direction=.west)∨(cut.actor.pushSource=some 214∧cut.direction=.east) := by
 have actual:=(NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached).1
 have allUnique : ∀i,(selected i).Nodup := by decide +kernel
 have groupUnique : (selected i).Nodup := allUnique i
 have groupInside : selected i⊆state.boulders := fun c h=>physical ((selected_perm i).mem_iff.mp h)
 have good : OwnedCorral11.Good locks region state (selected i) := ⟨i,hero,fun c h=>(selected_perm i).mem_iff.mpr h⟩
 obtain ⟨cut⟩:=Upper216Eight11.first_any closed unique nonempty logged actual groupUnique groupInside good reached.holes_sublist.subset gone
 obtain ⟨j,heroBefore,retained⟩:=Upper216Eight11.quiet_good_any closed unique cut.before actual groupUnique groupInside good reached.holes_sublist.subset
 have beforeFacts:=cut.before.logged.end_subset actual (selected i) groupUnique groupInside
 have beforeReached:=reached.append cut.before.logged.trace
 have nextReached:=beforeReached.append (Trace.cons cut.headChecked (Trace.nil cut.actor.state))
 have allBound : ∀i,(selected i).length≤18 := by decide +kernel
 have nextFacts:=Upper216Eight11.next_facts cut reached groupUnique groupInside (allBound i)
 obtain ⟨source,owner,metadata,pays⟩:=cut.headPaid
 have sourceLock : source∈locks j := by
  by_cases member : source∈locks j
  ·exact member
  ·exfalso
   have absent := member
   have whole : source::locks j⊆endGroup (selected i) cut.beforeOutcomes := List.cons_subset.mpr ⟨owner,retained⟩
   have card:=List.Nodup.length_le_of_subset (List.nodup_cons.mpr ⟨absent,unique j⟩) whole
   have bound:=endGroup_length_le (selected i) cut.beforeOutcomes
   have sizes:∀i,(selected i).length=4∧(locks i).length=4:=by decide +kernel
   have one:=sizes i;have two:=sizes j;simp only[List.length_cons] at card;omega
 have admitted:=Left188Pocket11.head_allowed locks region source (fun d=>¬paid source d∨allowed source d) j
  (heads j source sourceLock) cut.headChecked metadata heroBefore (step_player_clear _ _ _ _ cut.headChecked).1 (List.Subset.trans retained beforeFacts.2)
 have allowed:=admitted.resolve_left (fun h=>h pays)
 have dead {landing : Cell} (targets : pushTargets soko1_1.board source cut.direction=[landing])
  (unfilled : landing∉soko1_1.initial.holes) (frozen : List Cell) (locked : Locked soko1_1.board frozen)
  (shift : frozen⊆landing::(locks j).erase source) (member : landing∈frozen) : False := by
  have shape:=UpperHeadCases11.ordinary_effect cut.headChecked cut.headEffect metadata targets unfilled beforeReached.holes_sublist.subset
  have kept:=CageFour12.shifted_inside (unique j) retained owner shift
  have current : frozen⊆Upper216Eight11.next cut := by simpa only[Upper216Eight11.next,shape] using kept
  have owns : landing∈Upper216Eight11.next cut := by
   change landing∈update (endGroup (selected i) cut.beforeOutcomes) cut.headOutcome
   rw[shape];simp[update,move,owner,post]
  exact Upper216Eight11.frozen_absurd cut.after (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant nextReached).1
   nextFacts.1 nextFacts.2.1 locked (List.Subset.trans current nextFacts.2.1) member owns (Upper216Eight11.tail_gone cut gone)
 rcases allowed with ⟨rfl,west⟩|⟨rfl,directions⟩|⟨rfl,east⟩|⟨rfl,east⟩
 ·have shift:∀j:Fin 2,[183]⊆183::(locks j).erase 184:=by decide +kernel
  exact False.elim (dead (by rw[west];decide +kernel) (by decide +kernel) [183] frozen183 (shift j) (by simp))
 ·rcases directions with east|west
  ·have shift:∀j:Fin 2,[186,187]⊆186::(locks j).erase 185:=by decide +kernel
   exact False.elim (dead (by rw[east];decide +kernel) (by decide +kernel) [186,187] frozen186187 (shift j) (by simp))
  ·exact ⟨cut,Or.inl ⟨metadata,west⟩⟩
 ·have shift:∀j:Fin 2,[188,189]⊆188::(locks j).erase 187:=by decide +kernel
  exact False.elim (dead (by rw[east];decide +kernel) (by decide +kernel) [188,189] frozen188189 (shift j) (by simp))
 ·exact ⟨cut,Or.inr ⟨metadata,east⟩⟩
#print axioms first_exit

/-- The unavoidable exit is charged only to the two Left identities. -/
theorem future_two {state final history dirs past pastMoves pushes moves outcomes}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (i : Fin 2) (physical : locks i⊆state.boulders) (hero : state.player∈region i)
 (gone : endGroup (selected i) outcomes=[]) :
 2≤energy state final (left i) outcomes := by
 have actual:=(NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached).1
 have uniqueSelected : ∀i,(selected i).Nodup := by decide +kernel
 have uniqueLeft : ∀i,(left i).Nodup := by decide +kernel
 have leftBound : ∀i,(left i).length≤18 := by decide +kernel
 have groupInside : selected i⊆state.boulders := fun c h=>physical ((selected_perm i).mem_iff.mp h)
 have leftInside : left i⊆state.boulders := fun c h=>groupInside (List.mem_append_left _ h)
 have upperInside : [187,189]⊆state.boulders := fun c h=>groupInside (List.mem_append_right _ h)
 obtain ⟨cut,exit⟩:=first_exit reached logged i physical hero gone
 have fixed187:=no_push_unchanged [187] cut.beforeOutcomes
  (cut.before.fixed (List.mem_append_right _ (by simp)) (by intro d;exact Or.inr (Or.inr (Or.inl rfl))))
 have fixed189:=no_push_unchanged [189] cut.beforeOutcomes
  (cut.before.fixed (List.mem_append_right _ (by simp)) (by intro d;exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
 have upperSplit:=cut.before.logged.end_split actual [187] [189] (by decide +kernel) upperInside
 rw[fixed187,fixed189] at upperSplit
 have split:=cut.before.logged.end_split actual (left i) [187,189] (uniqueSelected i) groupInside
 have facts:=cut.before.logged.end_subset actual (left i) (uniqueLeft i) leftInside
 have beforeReached:=reached.append cut.before.logged.trace
 have valid:=NetHack.SokobanLinearPhases.Map11.trace_phase_invariant beforeReached
 obtain ⟨source,owner,metadata,pays⟩:=cut.headPaid
 have sourceCases : (source=185∧cut.direction=.west)∨(source=214∧cut.direction=.east) := by
  rcases exit with ⟨same,direction⟩|⟨same,direction⟩
  ·exact Or.inl ⟨Option.some.inj (metadata.symm.trans same),direction⟩
  ·exact Or.inr ⟨Option.some.inj (metadata.symm.trans same),direction⟩
 have leftOwner : source∈endGroup (left i) cut.beforeOutcomes := by
  rcases List.mem_append.mp (split.mem_iff.mpr owner) with owns|upper
  ·exact owns
  ·have member : source∈([187,189]:List Cell) := upperSplit.mem_iff.mpr upper
   rcases sourceCases with ⟨rfl,_⟩|⟨rfl,_⟩ <;>simp at member
 have row : 2≤charge NetHack.Soko11Hero315.holeWeight (endGroup (left i) cut.beforeOutcomes) cut.headOutcome+
   value cut.actor.state (update (endGroup (left i) cut.beforeOutcomes) cut.headOutcome)-
   value cut.middle (endGroup (left i) cut.beforeOutcomes) := by
  rcases sourceCases with ⟨rfl,west⟩|⟨rfl,east⟩
  ·exact LeftStrict11.exit_row scalar rfl valid cut.headChecked cut.headEffect facts.1 facts.2
    ⟨185,leftOwner,metadata,by simp[LeftActor11.Exit,west]⟩
  ·have checked : step soko1_1.board cut.middle .east=some cut.actor := by simpa only[east] using cut.headChecked
   have shape:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
    (show pushTargets soko1_1.board 214 .east=[215] by decide +kernel) (by decide +kernel) beforeReached.holes_sublist.subset
   have effect : Matches cut.middle cut.actor (.push 214 (.stay 215)) := by simpa only[shape] using cut.headEffect
   have heroEq:=ActorPrices11.support_of_check 214 cut.middle.player .east 213 (by decide +kernel)
    (step_player_clear _ _ _ _ checked).1 (PairPost11.source_adjacent checked metadata)
   obtain ⟨phase,atIndex⟩:=valid.2
   have phaseEq:=HazardPhaseCountedCorrection.at_phase NetHack.SokobanLinearPhases.Map11.certificate phase cut.middle atIndex
   have within : HazardPhases.At NetHack.SokobanLinearPhases.Map11.certificate
    (HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes cut.middle) cut.middle := by rw[←phaseEq];exact atIndex
   have active : HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes cut.middle<16 :=
    HazardPhaseCountedCorrection.active_of_step _ _ within _ _ checked
   have price:=of_decide_eq_true (List.all_eq_true.mp price214 _ (List.mem_range.mpr active))
   have bound : 2≤1+scalar.weight (HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes cut.middle) 214 215-
     scalar.weight (HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes cut.middle) cut.middle.player 214 := by
    rw[heroEq];exact price
   have owned:=OwnedStrict11.owned_stay_bound scalar cut.middle .east cut.actor valid checked 214 215 effect
    (endGroup (left i) cut.beforeOutcomes) facts.1 facts.2 leftOwner 2 bound
   change 2≤charge NetHack.Soko11Hero315.holeWeight (endGroup (left i) cut.beforeOutcomes) (.push 214 (.stay 215))+
    value cut.actor.state (update (endGroup (left i) cut.beforeOutcomes) (.push 214 (.stay 215)))-value cut.middle (endGroup (left i) cut.beforeOutcomes) at owned
   simpa only[shape] using owned
 have prefixNN:=HeroLedger.Logged.energy_nonnegative cut.before.logged (groupCertificate 18)
  (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached) (left i) (uniqueLeft i) leftInside (leftBound i)
 have afterActual:=step_boulders_nodup _ _ _ _ valid.1 cut.headChecked
 have afterUnique:=GhostSubset.update_unique _ _ _ cut.headEffect afterActual _ facts.1 facts.2
 have afterInside:=GhostSubset.update_subset _ _ _ cut.headEffect _ facts.1 facts.2
 have afterBound:=Nat.le_trans (update_length (endGroup (left i) cut.beforeOutcomes) cut.headOutcome)
  (Nat.le_trans (endGroup_length_le (left i) cut.beforeOutcomes) (leftBound i))
 have afterValid:=(groupCertificate 18).preserved _ _ _ valid cut.headChecked
 have tailNN:=HeroLedger.Logged.energy_nonnegative cut.after (groupCertificate 18) afterValid _ afterUnique afterInside afterBound
 change 0≤energy state cut.middle (left i) cut.beforeOutcomes at prefixNN
 change 0≤energy cut.actor.state final (update (endGroup (left i) cut.beforeOutcomes) cut.headOutcome) cut.afterOutcomes at tailNN
 have sum:=energy_append state cut.middle final (left i) cut.beforeOutcomes (cut.headOutcome::cut.afterOutcomes)
 have one:=OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight cut.middle cut.actor.state final
  (endGroup (left i) cut.beforeOutcomes) cut.headOutcome cut.afterOutcomes
 change energy cut.middle final (endGroup (left i) cut.beforeOutcomes) (cut.headOutcome::cut.afterOutcomes)=
  charge NetHack.Soko11Hero315.holeWeight (endGroup (left i) cut.beforeOutcomes) cut.headOutcome+
  value cut.actor.state (update (endGroup (left i) cut.beforeOutcomes) cut.headOutcome)-value cut.middle (endGroup (left i) cut.beforeOutcomes)+
  energy cut.actor.state final (update (endGroup (left i) cut.beforeOutcomes) cut.headOutcome) cut.afterOutcomes at one
 have same:=congrArg (energy state final (left i)) cut.outcomesEq
 omega
#print axioms future_two

/-- Permutation wrapper for the two current original Left identities. -/
theorem future_two_perm {state final history dirs past pastMoves pushes moves outcomes}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (i : Fin 2) (physical : locks i⊆state.boulders) (hero : state.player∈region i)
 (group pair : List Cell) (sameGroup : group.Perm (selected i)) (samePair : pair.Perm (left i))
 (gone : endGroup group outcomes=[]) :
 2≤energy state final pair outcomes := by
 have equivalent:=endGroup_perm sameGroup outcomes
 have selectedGone : endGroup (selected i) outcomes=[] := by
  rw[gone] at equivalent
  exact (List.perm_nil.mp equivalent.symm)
 have lower:=future_two reached logged i physical hero selectedGone
 have equal:=Hero315Frame11.energy_perm samePair state final outcomes
 omega
#print axioms future_two_perm
end Owner1007.Post214LeftTwo11
