import Owner1007.Hero315Frame11
import Owner1007.FullSurvivor11
namespace Owner1007.Upper188TagPrice11
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
def check (phase : Nat) : Bool :=
 (NetHack.SokobanLinearPhases.Map11.certificate.heroes phase).all fun hero=>
  decide (-23≤NetHack.Soko11Hero315.weight phase hero 187)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked : (List.range 17).all check=true := by decide +kernel
theorem values {state : State}
 (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state) :
 -23≤value state [187] := by
 obtain ⟨phase,atIndex⟩:=valid.2
 have bound : phase<17 := by have bound:=atIndex.1;change phase≤16 at bound;omega
 have row := of_decide_eq_true (List.all_eq_true.mp
  (List.all_eq_true.mp checked phase (List.mem_range.mpr bound)) state.player atIndex.2.2.1)
 have phaseEq := HazardPhaseCountedCorrection.at_phase NetHack.SokobanLinearPhases.Map11.certificate phase state atIndex
 simpa only [value,weightSum,weightAt,phaseEq,Int.add_zero] using row
theorem at_cell {dirs state pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs state pushes moves outcomes)
 (cell : Cell) (different : cell≠188) (tag : endGroup [188] outcomes=[cell])
 (floorValue : Int) (current : floorValue≤value state [cell]) :
 floorValue+25≤energy soko1_1.initial state [188] outcomes := by
 have positive : 1≤ownPushes [188] outcomes := by
  by_cases zero : ownPushes [188] outcomes=0
  ·have fixed:=no_push_unchanged [188] outcomes zero
   rw [tag] at fixed
   have same : cell=188 := by simpa only [List.cons.injEq,and_true] using fixed
   exact False.elim (different same)
  ·omega
 have sameLength : (endGroup [188] outcomes).length=([188] : List Cell).length := by rw [tag];rfl
 have credits := full_survivor_credits_zero (HeroLedger.holeOnly NetHack.Soko11Hero315.holeWeight) [188] outcomes sameLength
 have charges := HeroLedger.charges_eq_own NetHack.Soko11Hero315.holeWeight [188] outcomes
 have initial : value soko1_1.initial [188]= -24 := by decide +kernel
 unfold Hero315Frame11.energy HeroLedger.energy
 rw [charges,credits,tag,initial]
 simp only [Int.sub_zero,Int.ofNat_eq_natCast]
 omega
theorem at187_two {dirs state pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs state pushes moves outcomes)
 (tag : endGroup [188] outcomes=[187]) :
 2≤energy soko1_1.initial state [188] outcomes := by
 have current := values (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant logged.trace)
 exact at_cell logged 187 (by decide) tag (-23) current
#print axioms at187_two
end Owner1007.Upper188TagPrice11
