import Owner1007.Gate265Transport11Checks
import Owner1007.TransportQuiet11
namespace Owner1007.Gate265Transport11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.UpperFirstCut11
theorem region_closed (region : List Cell)
 (checks : ∀dir,directionCheck region dir=true) :
 ∀source dir dest,source∈region→¬paid source dir→dest∈pushTargets soko1_1.board source dir→dest∈region := by
 intro source dir dest member unpaid target
 have row := List.all_eq_true.mp (checks dir) source member
 unfold directionCheck at row
 simp only [if_neg unpaid] at row
 exact of_decide_eq_true (List.all_eq_true.mp row dest target)
theorem lower_closed :
 ∀source dir dest,source∈lower→¬paid source dir→dest∈pushTargets soko1_1.board source dir→dest∈lower := by
 apply region_closed lower
 intro dir
 cases dir
 ·exact lower_0
 ·exact lower_1
 ·exact lower_2
 ·exact lower_3
 ·exact lower_4
 ·exact lower_5
 ·exact lower_6
 ·exact lower_7
theorem upper_closed :
 ∀source dir dest,source∈upper→¬paid source dir→dest∈pushTargets soko1_1.board source dir→dest∈upper := by
 apply region_closed upper
 intro dir
 cases dir
 ·exact upper_0
 ·exact upper_1
 ·exact upper_2
 ·exact upper_3
 ·exact upper_4
 ·exact upper_5
 ·exact upper_6
 ·exact upper_7

theorem quiet_lower {dirs state pushes moves outcomes}
 (quiet : UpperQuiet11.Quiet paid soko1_1.initial soko1_1.initial.boulders dirs state pushes moves outcomes) :
 endGroup lowerOrigins outcomes⊆lower ∧(endGroup lowerOrigins outcomes).length=8 := by
 have projected := TransportQuiet11.Quiet.project quiet (by decide) (by decide) (by simp)
   lowerOrigins (by decide) (by decide)
 have moved := TransportQuiet11.Quiet.transport projected lower lower_closed lower_initial true
   (by intro _ c h;exact of_decide_eq_true (List.all_eq_true.mp lower_noholes c h)) (by simp)
 exact ⟨moved.1,moved.2 rfl⟩
theorem quiet_upper {dirs state pushes moves outcomes}
 (quiet : UpperQuiet11.Quiet paid soko1_1.initial soko1_1.initial.boulders dirs state pushes moves outcomes) :
 endGroup upperOrigins outcomes⊆upper := by
 have projected := TransportQuiet11.Quiet.project quiet (by decide) (by decide) (by simp)
   upperOrigins (by decide) (by decide)
 exact (TransportQuiet11.Quiet.transport projected upper upper_closed upper_initial false (by intro h;contradiction) (by simp)).1

theorem first_cut {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes) (completed : Goal final) :
 Nonempty (FirstCut paid soko1_1.initial soko1_1.initial.boulders dirs final pushes moves outcomes) := by
 rcases first_cut_or_quiet (paid:=paid) logged soko1_1.initial.boulders with found|quiet
 ·exact found
 ·have lowerCount := (quiet_lower quiet).2
  have inside := (logged.end_subset (by decide) lowerOrigins (by decide) (by decide)).2
  have unique := (logged.end_subset (by decide) lowerOrigins (by decide) (by decide)).1
  have count := List.Nodup.length_le_of_subset unique inside
  have conservation := logged.trace.conservation
  have empty : final.holes=[] := completed
  rw [empty] at conservation
  change 18+0=final.boulders.length+16 at conservation
  omega
#print axioms lower_closed
#print axioms upper_closed
#print axioms quiet_lower
#print axioms quiet_upper
#print axioms first_cut
end Owner1007.Gate265Transport11
