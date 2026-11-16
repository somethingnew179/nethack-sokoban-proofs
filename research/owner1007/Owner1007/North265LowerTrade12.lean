import Owner1007.North265LowerTen12
import Owner1007.After265TradeNine12
namespace Owner1007.North265LowerTrade12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
open Owner1007.North265LowerTen12 (p Lower currentTriple triple_unique activation before_perm)
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem first265_lower_trade {dirs final pushes moves outcomes}
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
 (tag:endGroup [345] before=[NorthEvents12.current i]) :
 11≤energy p Lower outcomes∨(10≤energy p Lower outcomes∧2≤(endGroup Lower outcomes).length):=by
 have initialUnique:FirstSplit12.afterN.boulders.Nodup:=by decide +kernel
 have perm:=before_perm first i fixed tag
 have tripleInside:currentTriple i⊆endGroup Lower before:=fun _ h=>perm.mem_iff.mp h
 have middleReached:=NorthBound12.north_reached.append first.trace
 have middleUnique:=middleReached.boulders_nodup (by decide +kernel)
 have old:=first.end_subset initialUnique Lower (by decide +kernel) (by decide +kernel)
 have actualInside:=List.Subset.trans tripleInside old.2
 have nextReached:=middleReached.append (Trace.cons checked (Trace.nil t.state))
 have nextActual:=step_boulders_nodup _ _ _ _ middleUnique checked
 have nextUnique:=GhostSubset.update_unique middle t (.push 265 (.stay 291)) effect nextActual
   (endGroup Lower before) old.1 old.2
 have nextSubset:=GhostSubset.update_subset middle t (.push 265 (.stay 291)) effect
   (endGroup Lower before) old.1 old.2
 obtain ⟨result,adjacent,push⟩:=effect_push_data checked effect
 obtain ⟨dest,next,_,_,clear⟩:=(push_first_clear soko1_2.board middle 265 .south result push).2
 have destEq:dest=291:=Option.some.inj (next.symm.trans (by decide +kernel))
 have clear291:291∉middle.boulders:=by simpa only[destEq] using clear
 have small:i.val<4:=by
   by_cases yes:i.val<4
   · exact yes
   · have val:i.val=4:=by have h:=i.isLt;omega
     have same:i=(4:Fin 5):=Fin.ext val
     subst i
     exact False.elim (clear291 (actualInside (by decide +kernel)))
 let j:Fin 4:=⟨i.val,small⟩
 have owner:265∈endGroup Lower before:=tripleInside (by simp[currentTriple])
 have nextInside:=CageFour12.shifted_inside (triple_unique i) tripleInside owner (activation i j rfl)
 have nextHero:t.state.player∈After26512.region j:=by
   rw[matches_hero middle t (.push 265 (.stay 291)) effect]
   exact After26512.start_hero j
 have later:=After265TradeNine12.energy_nine_or_two last nextReached
   (update (endGroup Lower before) (.push 265 (.stay 291))) nextUnique nextSubset completed nextHero nextInside
 have nn:=first.ownSlack_nonnegative Generated.soko1_2_potential_valid Lower
 change 0≤ownSlack p Lower before at nn
 have price:slack p (.push 265 (.stay 291))=2:=by decide +kernel
 have whole:energy p Lower outcomes=ownSlack p Lower before+2+
   energy p (update (endGroup Lower before) (.push 265 (.stay 291))) after:=by
   rw[shape,energy_at_split]
   simp only[projectedOutcome,if_pos owner,price]
 rcases later with nine|⟨eight,two⟩
 ·change 9≤energy p (update (endGroup Lower before) (.push 265 (.stay 291))) after at nine
  exact Or.inl (by omega)
 ·change 8≤energy p (update (endGroup Lower before) (.push 265 (.stay 291))) after at eight
  have length:2≤(endGroup Lower outcomes).length:=by
   rw[shape,endGroup_append]
   exact two
  exact Or.inr ⟨by omega,length⟩
#print axioms first265_lower_trade
end Owner1007.North265LowerTrade12
