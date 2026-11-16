import Owner1007.Hero315Frame11
import Owner1007.FullSurvivor11
namespace Owner1007.Left186TagPrice11
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
def check (phase : Nat) : Bool :=
 (NetHack.SokobanLinearPhases.Map11.certificate.heroes phase).all fun hero=>
  decide (-21≤NetHack.Soko11Hero315.weight phase hero 185 ∧ -20≤NetHack.Soko11Hero315.weight phase hero 184)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked : (List.range 17).all check=true := by decide +kernel
theorem values {state : State}
 (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state) :
 -21≤value state [185] ∧ -20≤value state [184] := by
 obtain ⟨phase,atIndex⟩:=valid.2
 have bound : phase<17 := by have bound:=atIndex.1;change phase≤16 at bound;omega
 have row := of_decide_eq_true (List.all_eq_true.mp
  (List.all_eq_true.mp checked phase (List.mem_range.mpr bound)) state.player atIndex.2.2.1)
 have phaseEq := HazardPhaseCountedCorrection.at_phase NetHack.SokobanLinearPhases.Map11.certificate phase state atIndex
 simpa only [value,weightSum,weightAt,phaseEq,Int.add_zero] using row
theorem at_cell {dirs state pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs state pushes moves outcomes)
 (cell : Cell) (different : cell≠186) (tag : endGroup [186] outcomes=[cell])
 (floorValue : Int) (current : floorValue≤value state [cell]) :
 floorValue+23≤energy soko1_1.initial state [186] outcomes := by
 have positive : 1≤ownPushes [186] outcomes := by
  by_cases zero : ownPushes [186] outcomes=0
  ·have fixed:=no_push_unchanged [186] outcomes zero
   rw [tag] at fixed
   have same : cell=186 := by simpa only [List.cons.injEq,and_true] using fixed
   exact False.elim (different same)
  ·omega
 have sameLength : (endGroup [186] outcomes).length=([186] : List Cell).length := by rw [tag];rfl
 have credits := full_survivor_credits_zero (HeroLedger.holeOnly NetHack.Soko11Hero315.holeWeight) [186] outcomes sameLength
 have charges := HeroLedger.charges_eq_own NetHack.Soko11Hero315.holeWeight [186] outcomes
 have initial : value soko1_1.initial [186]= -22 := by decide +kernel
 unfold Hero315Frame11.energy HeroLedger.energy
 rw [charges,credits,tag,initial]
 simp only [Int.sub_zero,Int.ofNat_eq_natCast]
 omega
theorem at185_two {dirs state pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs state pushes moves outcomes)
 (tag : endGroup [186] outcomes=[185]) :
 2≤energy soko1_1.initial state [186] outcomes := by
 have current := (values (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant logged.trace)).1
 exact at_cell logged 185 (by decide) tag (-21) current
theorem at184_three {dirs state pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs state pushes moves outcomes)
 (tag : endGroup [186] outcomes=[184]) :
 3≤energy soko1_1.initial state [186] outcomes := by
 have current := (values (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant logged.trace)).2
 exact at_cell logged 184 (by decide) tag (-20) current
#print axioms checked
#print axioms at185_two
#print axioms at184_three
end Owner1007.Left186TagPrice11
