import Owner1007.NorthAfterTwoBudget12
import Owner1007.NorthTwoJPacket12
namespace Owner1007.NorthTwoJImpossible12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem impossible {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : 1+pushes≤228)
 (first : NorthFirstJ22812.FirstJ final outcomes)
 (cut : NorthTwoJPacket12.SecondJ first) : False := by
 obtain ⟨ds,pp,mm,prefixLogged⟩ := cut.prefix_log
 have headEq : AfterJBound12.headOutcome first.kind=Lower291ThreeHeads12.A cut.path := by
   rw [cut.firstKindEq]
   exact (NorthTwoJPacket12.first_data cut.path).1
 have replaceHead := congrArg (fun head=>first.before++head::first.after) headEq
 have replaceTail := congrArg (fun tail=>first.before++Lower291ThreeHeads12.A cut.path::tail) cut.shape
 have normalized : first.before++Lower291ThreeHeads12.A cut.path::
     (cut.between++Lower291ThreeHeads12.B cut.path::cut.after)=cut.prefixOutcomes++cut.after := by
   simp only [NorthTwoJPacket12.SecondJ.prefixOutcomes,List.append_assoc,List.cons_append,List.nil_append]
 have shape : outcomes=cut.prefixOutcomes++cut.after :=
   first.shape.trans (replaceHead.trans (replaceTail.trans normalized))
 have paid := cut.prefix_paid
 change 4≤ownSlack AfterTwoOrdinaryTrap12.p NorthBound12.J cut.prefixOutcomes at paid
 have coreTag := cut.j_tag
 change (endGroup NorthBound12.J cut.prefixOutcomes).Perm
   (AfterTwoOrdinaryTrap12.C (Lower291ThreeHeads12.kind cut.path)) at coreTag
 have hero := cut.post_hero
 change cut.actor.state.player∈AfterTwoOrdinaryTrap12.R (Lower291ThreeHeads12.kind cut.path) cut.phase at hero
 have inside := cut.post_locks
 change AfterTwoOrdinaryTrap12.K (Lower291ThreeHeads12.kind cut.path) cut.phase⊆
   endGroup NorthBound12.G cut.prefixOutcomes at inside
 exact NorthAfterTwoBudget12.impossible logged completed cheap shape prefixLogged cut.last paid
   (Lower291ThreeHeads12.kind cut.path) cut.phase coreTag hero inside
#print axioms impossible
end Owner1007.NorthTwoJImpossible12
