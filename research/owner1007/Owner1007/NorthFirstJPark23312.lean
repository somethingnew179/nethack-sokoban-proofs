import Owner1007.NorthFirstJParkFacts12
namespace Owner1007.NorthFirstJPark23312
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def J4 : List Cell := [210,237,238,263]
theorem first_j_then_park233 {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (cut : NorthFirstJ22812.FirstJ final outcomes)
 {betweenDirs middle betweenPushes betweenMoves between t afterDirs afterPushes afterMoves after}
 (shape : cut.after=between++.push 318 (.stay 317)::after)
 (gap : Logged soko1_2.board cut.actor.state betweenDirs middle betweenPushes betweenMoves between)
 (head : step soko1_2.board middle .west=some t) (effect : Matches middle t (.push 318 (.stay 317)))
 (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
 (i : Fin 5) (hero : middle.player∈AfterJ12.region cut.kind i)
 (locks : AfterJ12.locks cut.kind i⊆endGroup (update (endGroup NorthBound12.G cut.before) (AfterJBound12.headOutcome cut.kind)) between)
 (sTwo : 2≤energy p [213] outcomes)
 (fixed : ∀small : List Cell,small⊆AfterJ12.fixed cut.kind→endGroup small between=small) :
 233≤1+pushes := by
 have bottom:=NorthFirstJParkFacts12.bottom_cases logged completed cut shape gap head effect last i hero locks fixed
 have whole:=NorthWrap12.canonical_north logged
 let all:=.walk 397::.push 371 (.stay 345)::outcomes
 have alive318 : endGroup [318] all≠[] := by
  change endGroup (update [318] (.push 371 (.stay 345))) outcomes≠[]
  simpa only[show update [318] (.push 371 (.stay 345))=[318] by decide +kernel] using bottom.2.1
 have alive371 : endGroup [371] all≠[] := by
  change endGroup (update [371] (.push 371 (.stay 345))) outcomes≠[]
  simpa only[show update [371] (.push 371 (.stay 345))=[345] by decide +kernel] using bottom.2.2
 have gone:=RightConsumedEight12.right_gone_of_two_survive whole completed 318 371 (by decide) (by decide) (by decide) alive318 alive371
 have right:=RightConsumedEight12.right_eight whole completed gone
 have rightSame:=NorthWrap12.energy_north Final222.R outcomes
 rw[show update Final222.R (.push 371 (.stay 345))=Final222.R by decide +kernel] at rightSame
 change energy p Final222.R all=energy p Final222.R outcomes at rightSame
 change 8≤energy p Final222.R all at right
 have firstBound:=event_energy_le Generated.soko1_2_potential_valid J4 cut.first cut.last (AfterJBound12.headOutcome cut.kind)
 have prior:=cut.fixedBefore J4 (by decide +kernel)
 have member : ∀kind:Fin 2,AfterJBound12.startSource kind∈J4 := by decide +kernel
 have own : projectedOutcome J4 (AfterJBound12.headOutcome cut.kind)=AfterJBound12.headOutcome cut.kind := by
  simp only[AfterJBound12.headOutcome,projectedOutcome,if_pos (member cut.kind)]
 rw[prior,own,AfterJBound12.first_price] at firstBound
 change 2≤energy p J4 (cut.before++AfterJBound12.headOutcome cut.kind::cut.after) at firstBound
 have firstSame:=congrArg (energy p J4) cut.shape
 have jTwo : 2≤energy p J4 outcomes := by omega
 have upper:=RightEnergy12.raw_group_energy logged NorthBound12.north_reached PreCage12.U (by decide +kernel) (by decide +kernel) completed
 have bonus : RightEnergy12.cert.bonus FirstSplit12.afterN.player (PatternCorrection.project PreCage12.U)=2 := by decide +kernel
 rw[bonus] at upper
 change 2≤energy p PreCage12.U outcomes at upper
 have unique:FirstSplit12.afterN.boulders.Nodup:=by decide +kernel
 have a:=logged.energy_split unique p PreCage12.U (J4++([213]++NorthBound12.BottomN)) (by decide +kernel) (by decide +kernel)
 have b:=logged.energy_split unique p J4 ([213]++NorthBound12.BottomN) (by decide +kernel) (by decide +kernel)
 have c:=logged.energy_split unique p [213] NorthBound12.BottomN (by decide +kernel) (by decide +kernel)
 have mono:=logged.energy_mono Generated.soko1_2_potential_valid unique
  (PreCage12.U++(J4++([213]++NorthBound12.BottomN))) NorthPriceBalance12.Left
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
 change energy p (PreCage12.U++(J4++([213]++NorthBound12.BottomN))) outcomes≤energy p NorthPriceBalance12.Left outcomes at mono
 have total:=NorthPriceBalance12.total logged completed
 change energy p NorthPriceBalance12.Left outcomes+energy p Final222.R outcomes=Int.ofNat (1+pushes)-212 at total
 have seven:=bottom.1
 change 7≤energy p NorthBound12.BottomN outcomes at seven
 simp only[Int.ofNat_eq_natCast] at total
 omega
#print axioms first_j_then_park233
end Owner1007.NorthFirstJPark23312
