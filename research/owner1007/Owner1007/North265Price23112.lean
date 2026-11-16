import Owner1007.North265LowerTen12
import Owner1007.PreAccessFour12
import Owner1007.NorthParityPrice12
namespace Owner1007.North265Price23112
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
theorem first265_lower_231 {dirs final pushes moves outcomes}
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
 (tag:endGroup [345] before=[NorthEvents12.current i]) :231≤1+pushes :=by
 have ten := North265LowerTen12.first265_lower_ten logged completed shape first checked effect last i fixed tag
 change 10≤energy p North265LowerTen12.Lower outcomes at ten
 have four := PreAccessFour12.energy_four logged NorthBound12.north_reached (PreAccessFour12.locks 0)
   (PreAccessFour12.unique 0) (by decide +kernel) completed PreAccessFour12.hero371 (fun _ h=>h)
 change 4≤energy p (PreAccessFour12.locks 0) outcomes at four
 have split := logged.energy_split (show FirstSplit12.afterN.boulders.Nodup by decide +kernel) p
   (PreAccessFour12.locks 0) North265LowerTen12.Lower (by decide +kernel) (by decide +kernel)
 have perm : (PreAccessFour12.locks 0++North265LowerTen12.Lower).Perm NorthParityPrice12.Left := by decide +kernel
 have same := energy_perm p perm outcomes
 have fourteen : 14≤energy p NorthParityPrice12.Left outcomes := by omega
 have lowerSurvives := North265LowerTen12.first265_lower_survives logged completed shape first checked effect last i fixed tag
 have leftSurvives : endGroup NorthParityPrice12.Left outcomes≠[] := by
  intro gone
  have sub:=logged.end_mono (show FirstSplit12.afterN.boulders.Nodup by decide +kernel)
    North265LowerTen12.Lower NorthParityPrice12.Left (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw[gone] at sub
  have lowerGone : endGroup North265LowerTen12.Lower outcomes=[] :=
    List.eq_nil_iff_forall_not_mem.mpr (by intro c h;exact List.not_mem_nil (sub h))
  exact lowerSurvives lowerGone
 have right:=NorthLeftSurvival12.right_five logged completed leftSurvives
 change 5≤energy p Final222.R outcomes at right
 have total:=NorthPriceBalance12.total logged completed
 change energy p NorthParityPrice12.Left outcomes+energy p Final222.R outcomes=Int.ofNat (1+pushes)-212 at total
 simp only[Int.ofNat_eq_natCast] at total
 omega
#print axioms first265_lower_231
end Owner1007.North265Price23112
