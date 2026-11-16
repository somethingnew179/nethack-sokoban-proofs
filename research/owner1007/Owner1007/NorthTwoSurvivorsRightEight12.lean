import Owner1007.North31823112
namespace Owner1007.NorthTwoSurvivorsRightEight12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open Owner1007.TokenAccounting NetHack.Sokoban.GhostPartition
abbrev p := Generated.soko1_2Potential
/-- Two selected survivors outside Right occupy both original spare slots. -/
theorem right_eight {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (group : List Cell)
 (unique : (group++Final222.R).Nodup) (inside : group++Final222.R⊆FirstSplit12.afterN.boulders)
 (two : 2≤(endGroup group outcomes).length) : 8≤energy p Final222.R outcomes := by
 have initialUnique : FirstSplit12.afterN.boulders.Nodup := by decide +kernel
 have split:=logged.end_split initialUnique group Final222.R unique inside
 have retained:=logged.end_subset initialUnique (group++Final222.R) unique inside
 have capacity:=List.Nodup.length_le_of_subset retained.1 retained.2
 have conserved:=(NorthBound12.north_reached.append logged.trace).conservation
 have empty : final.holes=[] := completed
 rw[empty] at conserved
 change 20+0=final.boulders.length+18 at conserved
 have count:=split.length_eq
 rw[List.length_append] at count
 have rightGone : endGroup Final222.R outcomes=[] := List.eq_nil_of_length_eq_zero (by omega)
 have whole:=NorthWrap12.canonical_north logged
 let all:=.walk 397::.push 371 (.stay 345)::outcomes
 have gone : endGroup Final222.R all=[] := by
  change endGroup (update Final222.R (.push 371 (.stay 345))) outcomes=[]
  simpa only[show update Final222.R (.push 371 (.stay 345))=Final222.R by decide +kernel] using rightGone
 have bound:=RightConsumedEight12.right_eight whole completed gone
 have same:=NorthWrap12.energy_north Final222.R outcomes
 rw[show update Final222.R (.push 371 (.stay 345))=Final222.R by decide +kernel] at same
 change energy p Final222.R all=energy p Final222.R outcomes at same
 change 8≤energy p Final222.R all at bound
 omega
#print axioms right_eight
end Owner1007.NorthTwoSurvivorsRightEight12
