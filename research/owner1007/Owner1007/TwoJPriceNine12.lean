import Owner1007.NorthTwoJImpossibleEight12
import Owner1007.ConsumedParity12
namespace Owner1007.TwoJPriceNine12
open NetHack.Sokoban NetHack.Sokoban.HazardPattern
open Owner1007.TokenAccounting
abbrev p := Generated.soko1_2Potential

theorem g_nine {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (first : NorthFirstJ22812.FirstJ final outcomes)
 (second : NorthTwoJPacket12.SecondJ first) : 9≤energy p NorthBound12.G outcomes := by
 apply Int.le_of_not_gt
 intro wrong
 have eight : energy p NorthBound12.G outcomes≤8 := by omega
 exact NorthTwoJImpossibleEight12.impossible logged completed eight first second

/-- Two actual J heads require ten group units when all seven original
Lower identities are absorbed, independently of the whole push budget. -/
theorem consumed_ten {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (first : NorthFirstJ22812.FirstJ final outcomes)
 (second : NorthTwoJPacket12.SecondJ first) (gone : endGroup NorthBound12.G outcomes=[]) :
 10≤energy p NorthBound12.G outcomes := by
 have nine := g_nine logged completed first second
 have even := ConsumedParity12.consumed_even NorthBound12.north_reached logged completed NorthBound12.G
   (by decide +kernel) (by decide +kernel) gone (by decide +kernel)
 change (energy p NorthBound12.G outcomes)%2=0 at even
 omega
#print axioms g_nine
#print axioms consumed_ten
end Owner1007.TwoJPriceNine12
