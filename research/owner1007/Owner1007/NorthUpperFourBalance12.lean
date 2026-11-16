import Owner1007.NorthPriceBalance12
namespace Owner1007.NorthUpperFourBalance12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open Owner1007 Owner1007.TokenAccounting
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
theorem canonical_joint_bound {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (upper : 4≤energy p PreCage12.U outcomes) (reserve : Nat)
 (lower : Int.ofNat reserve≤energy p NorthActivation12.GS outcomes) :
 220+reserve≤1+pushes := by
 have split := logged.energy_split (by decide +kernel) p PreCage12.U NorthActivation12.GS
   (by decide +kernel) (by decide +kernel)
 change energy p NorthPriceBalance12.Left outcomes=
   energy p PreCage12.U outcomes+energy p NorthActivation12.GS outcomes at split
 have right := NorthPriceBalance12.right_four logged completed
 change 4≤energy p Final222.R outcomes at right
 have all := NorthPriceBalance12.total logged completed
 change energy p NorthPriceBalance12.Left outcomes+energy p Final222.R outcomes=
   Int.ofNat (1+pushes)-212 at all
 simp only [Int.ofNat_eq_natCast] at all lower
 omega
#print axioms canonical_joint_bound
end Owner1007.NorthUpperFourBalance12
