import Owner1007.Left184213Right11Data
namespace Owner1007.Left184213Right11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem complete (i : Fin 2) (group : List Cell) (bounded : group.length≤4)
 (selected : locks i⊆group) (source : Cell) (owner : source∈group) : source∈locks i:=by
 by_cases member : source∈locks i
 ·exact member
 ·have all : source::locks i⊆group:=by intro c h;rcases List.mem_cons.mp h with rfl|later;exact owner;exact selected later
  have card:=List.Nodup.length_le_of_subset (List.nodup_cons.mpr ⟨member,unique i⟩) all
  simp only [List.length_cons,size i] at card
  omega

theorem first_exit {state final history dirs past pastMoves pushes moves outcomes}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (i : Fin 2) (inside : locks i⊆state.boulders) (hero : state.player∈region i)
 (gone : endGroup (locks i) outcomes=[]) :
 ∃cut : FirstCut paid state (locks i) dirs final pushes moves outcomes,∃j : Fin 2,
  cut.middle.player∈region j ∧ locks j⊆endGroup (locks i) cut.beforeOutcomes ∧
  ((cut.actor.pushSource=some 189∧cut.direction=.east)∨
   (cut.actor.pushSource=some 213∧cut.direction=.south)∨
   (j.val=1∧cut.actor.pushSource=some 189∧cut.direction=.west)):=by
 have valid:=NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
 have good : OwnedCorral11.Good locks region state (locks i):=⟨i,hero,List.Subset.refl _⟩
 obtain ⟨cut⟩:=Upper216Eight11.first_any closed unique nonempty logged valid.1 (unique i) inside good reached.holes_sublist.subset gone
 obtain ⟨j,heroBefore,retained⟩:=Upper216Eight11.quiet_good_any closed unique cut.before valid.1 (unique i) inside good reached.holes_sublist.subset
 have beforeFacts:=cut.before.logged.end_subset valid.1 (locks i) (unique i) inside
 have beforeReached:=reached.append cut.before.logged.trace
 have afterReached:=beforeReached.append (Trace.cons cut.headChecked (Trace.nil cut.actor.state))
 have beforeBound : (endGroup (locks i) cut.beforeOutcomes).length≤4:=by
  have bound:=endGroup_length_le (locks i) cut.beforeOutcomes
  rw [size] at bound
  exact bound
 have afterFacts:=Upper216Eight11.next_facts cut reached (unique i) inside (by rw [size];omega)
 have afterGone:=Upper216Eight11.tail_gone cut gone
 have frozenCase : ∀pair : List Cell,∀a : Cell,Locked soko1_1.board pair→a∈pair→pair⊆Upper216Eight11.next cut→False:=by
  intro pair a locked member subset
  exact Upper216Eight11.frozen_absurd cut.after (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant afterReached).1
   afterFacts.1 afterFacts.2.1 locked (List.Subset.trans subset afterFacts.2.1) member (subset member) afterGone
 obtain ⟨source,owner,metadata,pays⟩:=cut.headPaid
 have member:=complete j _ beforeBound retained source owner
 rcases head_shape j heroBefore member (List.Subset.trans retained beforeFacts.2) cut.headChecked metadata pays with
  ⟨rfl,west⟩|⟨rfl,directions⟩|⟨rfl,directions⟩
 ·have checked : step soko1_1.board cut.middle .west=some cut.actor:=by simpa only [west] using cut.headChecked
  have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
   (show pushTargets soko1_1.board 186 .west=[185] by decide +kernel) (by decide +kernel) beforeReached.holes_sublist.subset
  have lifted:=update_mono (locks j) (endGroup (locks i) cut.beforeOutcomes) (unique j) retained cut.headOutcome
  have pair : [184,185]⊆Upper216Eight11.next cut:=by
   change _⊆update (endGroup (locks i) cut.beforeOutcomes) cut.headOutcome
   apply List.Subset.trans (l₂:=update (locks j) cut.headOutcome) _ lifted
   rw [headEq]
   have shift : ∀j,186∈locks j→[184,185]⊆update (locks j) (.push 186 (.stay 185)):=by decide +kernel
   exact shift j member
  exact False.elim (frozenCase [184,185] 184 (locked_of_check _ _ (by decide +kernel)) (by decide) pair)
 ·rcases directions with east|west
  ·exact ⟨cut,j,heroBefore,retained,Or.inl ⟨metadata,east⟩⟩
  ·obtain ⟨j,bound⟩:=j
   have cases : j=0∨j=1:=by omega
   rcases cases with rfl|rfl
   ·have checked : step soko1_1.board cut.middle .west=some cut.actor:=by simpa only [west] using cut.headChecked
    have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
     (show pushTargets soko1_1.board 189 .west=[188] by decide +kernel) (by decide +kernel) beforeReached.holes_sublist.subset
    have lifted:=update_mono (locks 0) (endGroup (locks i) cut.beforeOutcomes) (unique 0) retained cut.headOutcome
    have pair : [187,188]⊆Upper216Eight11.next cut:=by
     change _⊆update (endGroup (locks i) cut.beforeOutcomes) cut.headOutcome
     apply List.Subset.trans (l₂:=update (locks 0) cut.headOutcome) _ lifted
     rw [headEq]
     decide +kernel
    exact False.elim (frozenCase [187,188] 187 (locked_of_check _ _ (by decide +kernel)) (by decide) pair)
   ·exact ⟨cut,1,heroBefore,retained,Or.inr (Or.inr ⟨rfl,metadata,west⟩)⟩
 ·rcases directions with south|west
  ·exact ⟨cut,j,heroBefore,retained,Or.inr (Or.inl ⟨metadata,south⟩)⟩
  ·have checked : step soko1_1.board cut.middle .west=some cut.actor:=by simpa only [west] using cut.headChecked
   have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
    (show pushTargets soko1_1.board 213 .west=[212] by decide +kernel) (by decide +kernel) beforeReached.holes_sublist.subset
   have effect : Matches cut.middle cut.actor (.push 213 (.stay 212)):=by simpa only [headEq] using cut.headEffect
   have lifted:=update_mono (locks j) (endGroup (locks i) cut.beforeOutcomes) (unique j) retained cut.headOutcome
   have selected : Left184Pocket11.locks j⊆Upper216Eight11.next cut:=by
    change _⊆update (endGroup (locks i) cut.beforeOutcomes) cut.headOutcome
    apply List.Subset.trans (l₂:=update (locks j) cut.headOutcome) _ lifted
    rw [headEq]
    have shift : ∀j,Left184Pocket11.locks j⊆update (locks j) (.push 213 (.stay 212)):=by decide +kernel
    exact shift j
   have afterHero : cut.actor.state.player∈Left184Pocket11.region j:=by
    rw [effect.2]
    have all : ∀j,(213:Cell)∈Left184Pocket11.region j:=by decide +kernel
    exact all j
   exact False.elim (Left184Pocket11.impossible_gone afterReached cut.after (Upper216Eight11.next cut)
    afterFacts.1 afterFacts.2.1 ⟨j,afterHero,selected⟩ afterGone)
#print axioms first_exit
end Owner1007.Left184213Right11
