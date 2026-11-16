import Owner1007.North265LowerTrade12
import Owner1007.NorthTwoSurvivorsRightEight12
import Owner1007.NorthParityPrice23212
import Owner1007.PreAccessFour12
import Owner1007.NorthParityPrice12
namespace Owner1007.North265Price23212
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
theorem first265_lower_232 {dirs final pushes moves outcomes}
 (logged:Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed:Goal final)
 {beforeDirs beforePushes beforeMoves before middle t after afterDirs afterPushes afterMoves}
 (shape:outcomes=before++(.push 265 (.stay 291))::after)
 (first:Logged soko1_2.board FirstSplit12.afterN beforeDirs middle beforePushes beforeMoves before)
 (checked:step soko1_2.board middle .south=some t)
 (effect:Matches middle t (.push 265 (.stay 291)))
 (last:Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
 (i:Fin 5)
 (fixed:∀ small:List Cell,small⊆NorthEvents12.J→endGroup small before=small)
 (tag:endGroup [345] before=[NorthEvents12.current i]) :232≤1+pushes :=by
 have trade:=North265LowerTrade12.first265_lower_trade logged completed shape first checked effect last i fixed tag
 have four:=PreAccessFour12.energy_four logged NorthBound12.north_reached (PreAccessFour12.locks 0)
  (PreAccessFour12.unique 0) (by decide +kernel) completed PreAccessFour12.hero371 (fun _ h=>h)
 change 4≤energy p (PreAccessFour12.locks 0) outcomes at four
 have split:=logged.energy_split (show FirstSplit12.afterN.boulders.Nodup by decide +kernel) p
  (PreAccessFour12.locks 0) North265LowerTen12.Lower (by decide +kernel) (by decide +kernel)
 have perm : (PreAccessFour12.locks 0++North265LowerTen12.Lower).Perm NorthPriceBalance12.Left := by decide +kernel
 have same:=energy_perm p perm outcomes
 rcases trade with eleven|⟨ten,two⟩
 ·change 11≤energy p North265LowerTen12.Lower outcomes at eleven
  have fifteen : 15≤energy p NorthPriceBalance12.Left outcomes := by omega
  exact NorthParityPrice23212.fifteen_implies_232 logged completed fifteen
 ·change 10≤energy p North265LowerTen12.Lower outcomes at ten
  change 2≤(endGroup North265LowerTen12.Lower outcomes).length at two
  have eight:=NorthTwoSurvivorsRightEight12.right_eight logged completed North265LowerTen12.Lower (by decide +kernel) (by decide +kernel) two
  change 8≤energy p Final222.R outcomes at eight
  have total:=NorthPriceBalance12.total logged completed
  change energy p NorthPriceBalance12.Left outcomes+energy p Final222.R outcomes=Int.ofNat (1+pushes)-212 at total
  simp only[Int.ofNat_eq_natCast] at total
  omega
#print axioms first265_lower_232
end Owner1007.North265Price23212
