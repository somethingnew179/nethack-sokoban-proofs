import Owner1007.AfterTwoSeven12
import Owner1007.NorthTwoJPacket12
import Owner1007.ConsumedParity12
namespace Owner1007.TwoJPriceEleven12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
abbrev p:=Generated.soko1_2Potential
theorem g_eleven {dirs final pushes moves outcomes}
 (logged:Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed:Goal final) (first:NorthFirstJ22812.FirstJ final outcomes)
 (cut:NorthTwoJPacket12.SecondJ first):11≤energy p NorthBound12.G outcomes:=by
 obtain ⟨ds,pp,mm,prefixLogged⟩:=cut.prefix_log
 have headEq:AfterJBound12.headOutcome first.kind=Lower291ThreeHeads12.A cut.path:=by
  rw[cut.firstKindEq]
  exact (NorthTwoJPacket12.first_data cut.path).1
 have replaceHead:=congrArg (fun head=>first.before++head::first.after) headEq
 have replaceTail:=congrArg (fun tail=>first.before++Lower291ThreeHeads12.A cut.path::tail) cut.shape
 have normalized:first.before++Lower291ThreeHeads12.A cut.path::
   (cut.between++Lower291ThreeHeads12.B cut.path::cut.after)=cut.prefixOutcomes++cut.after:=by
  simp only[NorthTwoJPacket12.SecondJ.prefixOutcomes,List.append_assoc,List.cons_append,List.nil_append]
 have shape:outcomes=cut.prefixOutcomes++cut.after:=
  first.shape.trans (replaceHead.trans (replaceTail.trans normalized))
 have reached:=NorthBound12.north_reached.append prefixLogged.trace
 have initialUnique:FirstSplit12.afterN.boulders.Nodup:=by decide +kernel
 have facts:=prefixLogged.end_subset initialUnique NorthBound12.G (by decide +kernel) (by decide +kernel)
 have hero:=cut.post_hero
 change cut.actor.state.player∈AfterTwoOrdinaryTrap12.R (Lower291ThreeHeads12.kind cut.path) cut.phase at hero
 have inside:=cut.post_locks
 change AfterTwoOrdinaryTrap12.K (Lower291ThreeHeads12.kind cut.path) cut.phase⊆
  endGroup NorthBound12.G cut.prefixOutcomes at inside
 have later:=AfterTwoSeven12.energy_seven cut.last reached _ facts.1 facts.2 completed
  (Lower291ThreeHeads12.kind cut.path) cut.phase hero inside
 change 7≤energy p (endGroup NorthBound12.G cut.prefixOutcomes) cut.after at later
 have paid:=cut.prefix_paid
 change 4≤ownSlack p NorthBound12.J cut.prefixOutcomes at paid
 have mono:=prefixLogged.ownSlack_mono Generated.soko1_2_potential_valid initialUnique
  NorthBound12.J NorthBound12.G (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel)
 change ownSlack p NorthBound12.J cut.prefixOutcomes≤ownSlack p NorthBound12.G cut.prefixOutcomes at mono
 have ledger:=TokenAccounting.energy_append p NorthBound12.G cut.prefixOutcomes cut.after
 rw[←shape] at ledger
 omega

theorem consumed_twelve {dirs final pushes moves outcomes}
 (logged:Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed:Goal final) (first:NorthFirstJ22812.FirstJ final outcomes)
 (cut:NorthTwoJPacket12.SecondJ first) (gone:endGroup NorthBound12.G outcomes=[]):
 12≤energy p NorthBound12.G outcomes:=by
 have eleven:=g_eleven logged completed first cut
 have even:=ConsumedParity12.consumed_even NorthBound12.north_reached logged completed NorthBound12.G
  (by decide +kernel) (by decide +kernel) gone (by decide +kernel)
 change (energy p NorthBound12.G outcomes)%2=0 at even
 omega
#print axioms g_eleven
#print axioms consumed_twelve
end Owner1007.TwoJPriceEleven12
