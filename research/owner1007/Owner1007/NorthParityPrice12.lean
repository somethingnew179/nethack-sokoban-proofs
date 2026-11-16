import Owner1007.ConsumedParity12
import Owner1007.NorthPriceBalance12
namespace Owner1007.NorthParityPrice12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
abbrev Left := NorthPriceBalance12.Left
theorem thirteen_implies_230 {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (lower : 13≤energy p Left outcomes) :230≤1+pushes := by
 have total := NorthPriceBalance12.total logged completed
 change energy p Left outcomes+energy p Final222.R outcomes=Int.ofNat (1+pushes)-212 at total
 simp only [Int.ofNat_eq_natCast] at total
 by_cases gone:endGroup Left outcomes=[]
 · have even := ConsumedParity12.consumed_even NorthBound12.north_reached logged completed Left
     (by decide +kernel) (by decide +kernel) gone (by decide +kernel)
   change (energy p Left outcomes)%2=0 at even
   have right := NorthPriceBalance12.right_four logged completed
   change 4≤energy p Final222.R outcomes at right
   omega
 · have right := NorthLeftSurvival12.right_five logged completed gone
   change 5≤energy p Final222.R outcomes at right
   omega
#print axioms thirteen_implies_230
end Owner1007.NorthParityPrice12
