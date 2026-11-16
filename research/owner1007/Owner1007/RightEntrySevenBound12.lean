import Owner1007.RightEntrySevenCapacity12
import Owner1007.RightEntrySeven12
import Owner1007.RightCoreTwo12
import Owner1007.East22612
namespace Owner1007.RightEntrySeven12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
abbrev R := RightEnergy12.Right
def CoreTicket : Prop :=
 ∀ {state final dirs pushes moves outcomes}, Logged soko1_2.board state dirs final pushes moves outcomes→
 ∀ {history:List Dir}{past pastMoves:Nat},Trace soko1_2.board soko1_2.initial history state past pastMoves→
 ∀ group:List Cell,group.Nodup→group⊆state.boulders→Goal final→state.player=193→
 [141,167,168,194]⊆group→(2:Int)≤energy p group outcomes

theorem core_reserve : CoreTicket := by
 intro state final dirs pushes moves outcomes logged history past pastMoves reached group unique subset completed player inside
 exact RightCoreTwo12.energy_two logged reached group unique subset completed
   (by rw[player];decide +kernel) inside

theorem right_seven
 (matrix : PricedCorral11.checkExcept soko1_2.board soko1_2.initial.holes locks region paid=true)
 {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history:List Dir}{past pastMoves:Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (player:state.player=296) (inside:locks 0⊆state.boulders) (completed:Goal final) :
 7≤energy p R outcomes := by
 have closed:=PricedCorral11.closed_of_checkExcept _ _ _ _ _ matrix
 have actualUnique:=reached.boulders_nodup (by decide +kernel)
 have rightInside:=List.Subset.trans start_right inside
 rcases TaggedFlow12.event_or_good closed unique tag_inside tag_sound tag_update
   logged reached (locks 0) [271] [246] (unique 0) inside
   (i:=0) (by rw[player];exact start_hero) (fun _ h=>h) rfl rfl with event|terminal
 · obtain ⟨beforeDirs,beforePushes,beforeMoves,before,middle,dir,t,outcome,after,
     afterDirs,afterPushes,afterMoves,j,shape,first,checked,effect,last,heroBefore,locksOne,pays,sAt,tAt,unchanged⟩:=
     event.split_fixed fixed fixed_inside fixed_guard reached (unique 0) inside
   have middleReached:=reached.append first.trace
   have middleUnique:=middleReached.boulders_nodup (by decide +kernel)
   have oldGroup:=first.end_subset actualUnique (locks 0) (unique 0) inside
   have oldRight:=first.end_subset actualUnique R (by decide +kernel) rightInside
   have nextActual:=step_boulders_nodup _ _ _ _ middleUnique checked
   have nextUnique:=GhostSubset.update_unique middle t outcome effect nextActual
     (endGroup (locks 0) before) oldGroup.1 oldGroup.2
   have nextSubset:=GhostSubset.update_subset middle t outcome effect
     (endGroup (locks 0) before) oldGroup.1 oldGroup.2
   have nextRUnique:=GhostSubset.update_unique middle t outcome effect nextActual
     (endGroup R before) oldRight.1 oldRight.2
   have nextRSubset:=GhostSubset.update_subset middle t outcome effect
     (endGroup R before) oldRight.1 oldRight.2
   have nextReached:=middleReached.append (Trace.cons checked (Trace.nil t.state))
   cases outcome with
   | walk target=>exact False.elim pays
   | push source ending=>
     obtain ⟨owner,pays⟩:=pays
     obtain ⟨_,adjacent,_⟩:=effect_push_data checked effect
     have count:=endGroup_length_le (locks 0) before
     rw[sizes 0] at count
     have sourceInside:source∈locks j:=
       RightEntry12.member_of_tight (unique j) locksOne (by rw[sizes j];exact count) owner
     have cases:=head_classification j middle.player heroBefore dir source sourceInside adjacent pays
     have frozen (dest:Cell) (small:List Cell) (smallUnique:small.Nodup) (lock:Locked soko1_2.board small)
       (large:3≤small.length) (targets:pushTargets soko1_2.board source dir=[dest])
       (clear:dest∉soko1_2.initial.holes) (shift:small⊆dest::(locks j).erase source):False:=by
       have endingSame:=push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset targets clear checked effect
       subst ending
       have kept:=CageFour12.shifted_inside (unique j) locksOne owner shift
       have survives:=last.locked_end_inside nextActual
         (update (endGroup (locks 0) before) (.push source (.stay dest))) nextUnique nextSubset small lock kept
       have finalInside:=last.end_subset nextActual
         (update (endGroup (locks 0) before) (.push source (.stay dest))) nextUnique nextSubset
       have count:=List.Nodup.length_le_of_subset smallUnique (List.Subset.trans survives finalInside.2)
       rw[RightEntryCapacity12.final_two logged reached completed] at count
       omega
     rcases cases with marker|gate|back|square|triple
     · obtain ⟨rfl,rfl,shift⟩:=marker
       have endingSame:=push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 270 .north=[244] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have fixedPair:endGroup [218,270] before=[218,270]:=unchanged [218,270] (by decide +kernel)
       have pairOld:=first.end_subset actualUnique [218,270] (by decide +kernel)
         (List.Subset.trans (by decide +kernel) inside)
       have pairNextUnique:=GhostSubset.update_unique middle t (.push 270 (.stay 244)) effect nextActual
         (endGroup [218,270] before) pairOld.1 pairOld.2
       have pairNextSubset:=GhostSubset.update_subset middle t (.push 270 (.stay 244)) effect
         (endGroup [218,270] before) pairOld.1 pairOld.2
       have afterPair:[218,244]⊆update (endGroup [218,270] before) (.push 270 (.stay 244)):=by
         rw[fixedPair]
         decide +kernel
       have kept:=last.locked_end_inside nextActual
         (update (endGroup [218,270] before) (.push 270 (.stay 244))) pairNextUnique pairNextSubset [218,244] lockedPair afterPair
       have length:=List.Nodup.length_le_of_subset (show ([218,244]:List Cell).Nodup by decide +kernel) kept
       have pairFull:2≤(endGroup [218,270] outcomes).length:=by
         rw[shape,endGroup_append]
         simpa only[endGroup,List.length_cons,List.length_nil,Nat.add_zero] using length
       have eight:=RightEntrySevenCapacity12.eight_of_pair logged reached player
         (List.Subset.trans (show (R++[270])⊆locks 0 by decide +kernel) inside) completed pairFull
       change 8≤energy p R outcomes at eight
       omega
     · obtain ⟨rfl,rfl,rfl⟩:=gate
       have endingSame:=push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 193 .north=[167] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have atS:endGroup [271] before=[245]:=by simpa only[show tagS (3:Fin 4)=245 by decide +kernel] using sAt
       have atT:endGroup [246] before=[194]:=by simpa only[show tagT (3:Fin 4)=194 by decide +kernel] using tAt
       have sPrice:=RightEntry12.slack271_at245 before atS
       have tPrice:=RightEntrySevenCapacity12.low_at194_slack_two first reached player rightInside atT
       change 1≤ownSlack p [271] before at sPrice
       change 2≤ownSlack p [246] before at tPrice
       have split:=East22612.own_slack_split first actualUnique p [271] [246] (by decide +kernel)
         (List.Subset.trans (by decide +kernel) rightInside)
       have mono:=first.ownSlack_mono Generated.soko1_2_potential_valid actualUnique [271,246] R
         (by decide +kernel) (by decide +kernel) (List.Subset.trans (by decide +kernel) rightInside) rightInside (by decide +kernel)
       change ownSlack p [271,246] before=ownSlack p [271] before+ownSlack p [246] before at split
       change ownSlack p [271,246] before≤ownSlack p R before at mono
       have prefixPrice:3≤ownSlack p R before:=by omega
       have fixed141:endGroup [141] before=[141]:=unchanged [141] (by decide +kernel)
       have fixed168:endGroup [168] before=[168]:=unchanged [168] (by decide +kernel)
       have fixed193:endGroup [193] before=[193]:=unchanged [193] (by decide +kernel)
       have i141:=first.member_end_subset actualUnique R (by decide +kernel) rightInside 141 (by decide +kernel)
       have i168:=first.member_end_subset actualUnique R (by decide +kernel) rightInside 168 (by decide +kernel)
       have i193:=first.member_end_subset actualUnique R (by decide +kernel) rightInside 193 (by decide +kernel)
       have i246:=first.member_end_subset actualUnique R (by decide +kernel) rightInside 246 (by decide +kernel)
       rw[fixed141] at i141
       rw[fixed168] at i168
       rw[fixed193] at i193
       rw[atT] at i246
       have coreBefore:[141,168,193,194]⊆endGroup R before:=by
         intro c h
         simp only[List.mem_cons,List.not_mem_nil,or_false] at h
         rcases h with rfl|rfl|rfl|rfl
         · exact i141 (by decide +kernel)
         · exact i168 (by decide +kernel)
         · exact i193 (by decide +kernel)
         · exact i246 (by decide +kernel)
       have own193:193∈endGroup R before:=i193 (by decide +kernel)
       have nextCore:=CageFour12.shifted_inside (show ([141,168,193,194]:List Cell).Nodup by decide +kernel)
         coreBefore own193
         (show [141,167,168,194]⊆167::([141,168,193,194]:List Cell).erase 193 by decide +kernel)
       have later:=core_reserve last nextReached (update (endGroup R before) (.push 193 (.stay 167))) nextRUnique nextRSubset completed
         (matches_hero middle t (.push 193 (.stay 167)) effect) nextCore
       have one:slack p (.push 193 (.stay 167))=2:=by decide +kernel
       have seven:7≤energy p R outcomes:=by
         rw[shape,energy_at_split]
         simp only[projectedOutcome,if_pos own193,one]
         omega
       exact seven
     · obtain ⟨rfl,rfl,rfl⟩:=back
       have endingSame:=push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 245 .south=[271] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have atS:endGroup [271] before=[245]:=by simpa only[show tagS (3:Fin 4)=245 by decide +kernel] using sAt
       have atT:endGroup [246] before=[194]:=by simpa only[show tagT (3:Fin 4)=194 by decide +kernel] using tAt
       have sPrice:=RightEntry12.slack271_at245 before atS
       have tPrice:=RightEntrySevenCapacity12.low_at194_slack_two first reached player rightInside atT
       change 1≤ownSlack p [271] before at sPrice
       change 2≤ownSlack p [246] before at tPrice
       have later:=last.energy_nonnegative Generated.soko1_2_potential_valid [271]
       change 0≤energy p [271] after at later
       have sWhole:2≤energy p [271] outcomes:=by
         rw[shape,energy_at_split,atS]
         change 2≤ownSlack p [271] before+1+energy p [271] after
         omega
       have suffix:=Logged.cons checked effect last
       have tBound:=prefix_slack_le_energy Generated.soko1_2_potential_valid [246] before ((.push 245 (.stay 271))::after) suffix
       change ownSlack p [246] before≤energy p [246] (before++(.push 245 (.stay 271))::after) at tBound
       have tWhole:2≤energy p [246] outcomes:=by rw[shape];omega
       exact RightEntrySevenCapacity12.seven_of_both_two logged reached player rightInside completed tWhole sWhole
     · obtain ⟨rfl,rfl,shift⟩:=square
       exact False.elim (frozen 219 [192,193,218,219] (by decide +kernel) lockedSquare (by decide +kernel)
         (by decide +kernel) (by decide +kernel) shift)
     · obtain ⟨rfl,rfl,shift⟩:=triple
       exact False.elim (frozen 244 [218,244,270] (by decide +kernel) lockedTriple (by decide +kernel)
         (by decide +kernel) (by decide +kernel) shift)
 · obtain ⟨j,hero,locksOne,_,_⟩:=terminal
   have finalInside:=logged.end_subset actualUnique (locks 0) (unique 0) inside
   have count:=List.Nodup.length_le_of_subset (unique j) (List.Subset.trans locksOne finalInside.2)
   rw[sizes j,RightEntryCapacity12.final_two logged reached completed] at count
   omega
#print axioms right_seven
end Owner1007.RightEntrySeven12
