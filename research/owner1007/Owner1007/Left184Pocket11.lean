import Owner1007.Left184Pocket11Data
import Owner1007.CageFour12
namespace Owner1007.Left184Pocket11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- This left pocket cannot lose all selected stones, at ANY energy price.
No Goal or global push budget is assumed. -/
theorem impossible_gone {state final history dirs past pastMoves pushes moves outcomes}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (group : List Cell) (uniqueGroup : group.Nodup) (inside : group⊆state.boulders)
 (good : OwnedCorral11.Good locks region state group) (gone : endGroup group outcomes=[]) : False := by
 have actual := (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached).1
 obtain ⟨cut⟩ := Upper216Eight11.first_any closed unique nonempty logged actual uniqueGroup inside good reached.holes_sublist.subset gone
 obtain ⟨i,hero,retained⟩ := Upper216Eight11.quiet_good_any closed unique cut.before actual uniqueGroup inside good reached.holes_sublist.subset
 have old := cut.before.logged.end_subset actual group uniqueGroup inside
 have middleReached := reached.append cut.before.logged.trace
 have nextReached := middleReached.append (Trace.cons cut.headChecked (Trace.nil cut.actor.state))
 have nextActual := (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant nextReached).1
 have nextUnique := GhostSubset.update_unique _ _ _ cut.headEffect nextActual _ old.1 old.2
 have nextInside := GhostSubset.update_subset _ _ _ cut.headEffect _ old.1 old.2
 have nextGone := Upper216Eight11.tail_gone cut gone
 obtain ⟨source,owner,metadata,pays⟩ := cut.headPaid
 obtain ⟨which,west⟩:=pays
 have checked : step soko1_1.board cut.middle .west=some cut.actor := by simpa only [west] using cut.headChecked
 rcases which with rfl|rfl
 ·have shape := UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
    (show pushTargets soko1_1.board 212 .west=[211] by decide +kernel) (by decide +kernel) middleReached.holes_sublist.subset
  have effect : Matches cut.middle cut.actor (.push 212 (.stay 211)) := by simpa only [shape] using cut.headEffect
  have shift : [184,211]⊆211::(locks i).erase 212 := by
    have checked : ∀i:Fin 2,[184,211]⊆211::(locks i).erase 212 := by decide +kernel
    exact checked i
  have kept := CageFour12.shifted_inside (unique i) retained owner shift
  have current : [184,211]⊆Upper216Eight11.next cut := by simpa only [Upper216Eight11.next,shape] using kept
  have newHero : cut.actor.state.player∈LeftDeadSplit11.region 1 := by
    rw [effect.2]
    change (212:Cell)∈LeftDeadSplit11.region 1
    decide +kernel
  exact LeftDeadSplit11.impossible_gone nextReached cut.after (Upper216Eight11.next cut)
    nextUnique nextInside ⟨1,newHero,current⟩ nextGone
 ·have shape := UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
    (show pushTargets soko1_1.board 186 .west=[185] by decide +kernel) (by decide +kernel) middleReached.holes_sublist.subset
  have effect : Matches cut.middle cut.actor (.push 186 (.stay 185)) := by simpa only [shape] using cut.headEffect
  have shift : [184,185]⊆185::(locks i).erase 186 := by
    have checked : ∀i:Fin 2,[184,185]⊆185::(locks i).erase 186 := by decide +kernel
    exact checked i
  have kept := CageFour12.shifted_inside (unique i) retained owner shift
  have current : [184,185]⊆Upper216Eight11.next cut := by simpa only [Upper216Eight11.next,shape] using kept
  have physical := List.Subset.trans current nextInside
  exact Upper216Eight11.frozen_absurd cut.after nextActual nextUnique nextInside
    (locked_of_check _ [184,185] (by decide +kernel)) physical (by simp : (184:Cell)∈[184,185])
    (current (by simp)) nextGone
#print axioms impossible_gone
end Owner1007.Left184Pocket11
