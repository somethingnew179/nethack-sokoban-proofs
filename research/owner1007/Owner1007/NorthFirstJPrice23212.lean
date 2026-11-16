import Owner1007.NorthAfterFirstQuietTen23112
import Owner1007.NorthCritical23212
namespace Owner1007.NorthFirstJPrice23212
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
/-- An actual original FirstJ packet after spending S2 requires price232. -/
theorem first_j_lower232 {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (cut : NorthFirstJ22812.FirstJ final outcomes)
 (sTwo : 2≤energy p [213] outcomes) : 232≤1+pushes := by
 by_cases done : 232≤1+pushes
 ·exact done
 have cheap : 1+pushes≤231 := by omega
 have upper:=RightEnergy12.raw_group_energy logged NorthBound12.north_reached PreCage12.U
  (by decide +kernel) (by decide +kernel) completed
 have bonus : RightEnergy12.cert.bonus FirstSplit12.afterN.player (PatternCorrection.project PreCage12.U)=2 := by decide +kernel
 rw [bonus] at upper
 change 2≤energy p PreCage12.U outcomes at upper
 have leftCap : energy p NorthPriceBalance12.Left outcomes≤14 := by
  by_cases cap : energy p NorthPriceBalance12.Left outcomes≤14
  ·exact cap
  ·have fifteen : 15≤energy p NorthPriceBalance12.Left outcomes := by omega
   have bound:=NorthParityPrice23212.fifteen_implies_232 logged completed fifteen
   omega
 have gsSplit:=logged.energy_split (show FirstSplit12.afterN.boulders.Nodup by decide +kernel) p
  NorthBound12.G [213] (by decide +kernel) (by decide +kernel)
 change energy p NorthActivation12.GS outcomes=energy p NorthBound12.G outcomes+energy p [213] outcomes at gsSplit
 have leftSplit:=logged.energy_split (show FirstSplit12.afterN.boulders.Nodup by decide +kernel) p
  PreCage12.U NorthActivation12.GS (by decide +kernel) (by decide +kernel)
 change energy p NorthPriceBalance12.Left outcomes=energy p PreCage12.U outcomes+energy p NorthActivation12.GS outcomes at leftSplit
 have gCap : energy p NorthBound12.G outcomes≤10 := by omega
 obtain ⟨critical,quiet⟩:=NorthAfterFirstQuietTen23112.critical_required logged completed cheap sTwo gCap cut
 have bound:=NorthCritical23212.critical_lower232 logged completed cut critical quiet
 omega
#print axioms first_j_lower232
end Owner1007.NorthFirstJPrice23212
