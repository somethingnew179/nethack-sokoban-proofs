import Owner1007.RightParkedSix11Data
import Owner1007.QuietGroupFixed11
namespace Owner1007.RightParkedSix11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem first_exit {state final history dirs past pastMoves pushes moves outcomes}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (i : Fin 4) (physical : locks i⊆state.boulders) (hero : state.player∈region i)
 (gone : endGroup (locks i) outcomes=[]) :
 ∃cut : FirstCut paid state (locks i) dirs final pushes moves outcomes,
 ownPushes (locks i) cut.beforeOutcomes=0 ∧cut.middle.player∈region i ∧
 ∃source,source∈locks i∧cut.actor.pushSource=some source∧Shape i source cut.direction:=by
 have valid:=NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
 have good : OwnedCorral11.Good locks region state (locks i):=⟨i,hero,List.Subset.refl _⟩
 obtain ⟨cut⟩:=Upper216Eight11.first_any closed unique nonempty logged valid.1 (unique i) physical good reached.holes_sublist.subset gone
 have zero:=QuietGroupFixed11.whole_fixed cut.before (by intro c h d;trivial)
 have fixed:=no_push_unchanged (locks i) cut.beforeOutcomes zero
 have retained:=LeftQuietIdentity11.quiet_zero_static (locks i) (region i) paid (phase_closed i) (unique i)
  (by intro hero member source owner dir adjacent;exact Or.inr trivial)
  cut.before physical (List.Perm.refl _) hero reached.holes_sublist.subset
 have facts:=cut.before.logged.end_subset valid.1 (locks i) (unique i) physical
 rw [fixed] at facts
 obtain ⟨source,owner,metadata,_⟩:=cut.headPaid
 rw [fixed] at owner
 exact ⟨cut,zero,retained.2,source,owner,metadata,head_shape i retained.2 facts.2 owner cut.headChecked metadata⟩
#print axioms first_exit
end Owner1007.RightParkedSix11
