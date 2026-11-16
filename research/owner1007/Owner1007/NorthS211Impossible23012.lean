import Owner1007.NorthCritical23212
import Owner1007.NorthFirstJ23012
import Owner1007.North187ToS23012
namespace Owner1007.NorthS211Impossible23012
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential

theorem impossible {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : 1+pushes≤230)
 (stage : North187ToS23012.Stage final outcomes) : False := by
 obtain ⟨first⟩:=NorthFirstJ23012.after_s logged completed cheap stage.shape stage.first stage.last
  stage.phase stage.hero stage.inside stage.sAt stage.fixed stage.paid
 have nnS:=stage.last.energy_nonnegative Generated.soko1_2_potential_valid (endGroup [213] stage.before)
 change 0≤energy p (endGroup [213] stage.before) stage.after at nnS
 have sTwo : 2≤energy p [213] outcomes := by
  have equal:=TokenAccounting.energy_append p [213] stage.before stage.after
  rw[←stage.shape] at equal
  have prefixPrice:=stage.paid
  change 2≤ownSlack p [213] stage.before at prefixPrice
  omega
 have upper:=RightEnergy12.raw_group_energy logged NorthBound12.north_reached PreCage12.U
  (by decide +kernel) (by decide +kernel) completed
 have bonus : RightEnergy12.cert.bonus FirstSplit12.afterN.player (PatternCorrection.project PreCage12.U)=2 := by decide +kernel
 rw[bonus] at upper
 change 2≤energy p PreCage12.U outcomes at upper
 have right:=NorthPriceBalance12.right_four logged completed
 change 4≤energy p Final222.R outcomes at right
 have total:=NorthPriceBalance12.total logged completed
 change energy p NorthPriceBalance12.Left outcomes+energy p Final222.R outcomes=Int.ofNat (1+pushes)-212 at total
 simp only[Int.ofNat_eq_natCast] at total
 have leftCap : energy p NorthPriceBalance12.Left outcomes≤14 := by omega
 have gsSplit:=logged.energy_split (show FirstSplit12.afterN.boulders.Nodup by decide +kernel) p
  NorthBound12.G [213] (by decide +kernel) (by decide +kernel)
 change energy p NorthActivation12.GS outcomes=energy p NorthBound12.G outcomes+energy p [213] outcomes at gsSplit
 have leftSplit:=logged.energy_split (show FirstSplit12.afterN.boulders.Nodup by decide +kernel) p
  PreCage12.U NorthActivation12.GS (by decide +kernel) (by decide +kernel)
 change energy p NorthPriceBalance12.Left outcomes=energy p PreCage12.U outcomes+energy p NorthActivation12.GS outcomes at leftSplit
 have gCap : energy p NorthBound12.G outcomes≤10 := by omega
 obtain ⟨critical,quiet⟩:=NorthAfterFirstQuietTen12.critical_required logged completed cheap gCap first
 have bound:=NorthCritical23212.critical_lower232 logged completed first critical quiet
 omega
#print axioms impossible
end Owner1007.NorthS211Impossible23012
