import Owner1007.North22812
import Owner1007.North265Price23112
import Owner1007.North31823112
import Owner1007.North29123212
import Owner1007.RingEleven12
import Owner1007.NorthPriceBalance12
namespace Owner1007.NorthMain23112
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12 Owner1007.North22812
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem event_lower231 {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final)
 {beforeDirs beforePushes beforeMoves before middle dir t source ending after afterDirs afterPushes afterMoves}
 (i : Fin 10) (shape : outcomes=before++(.push source ending)::after)
 (first : Logged soko1_2.board FirstSplit12.afterN beforeDirs middle beforePushes beforeMoves before)
 (checked : step soko1_2.board middle dir=some t) (effect : Matches middle t (.push source ending))
 (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
 (hero : middle.player∈PreCage12.northRegion i) (locks : PreCage12.northLocks i⊆endGroup NorthTagFacts12.selected before)
 (sourceMember : source∈PreCage12.northLocks i) (pays : NorthEvents12.paid source dir)
 (sAt : endGroup [213] before=[PreCage12.northS i]) (tAt : endGroup [345] before=[PreCage12.northTag i])
 (unchanged : ∀ small : List Cell, small⊆NorthTagFacts12.fixed → endGroup small before=small) :
 231≤1+pushes := by
 have initialUnique : FirstSplit12.afterN.boulders.Nodup := by decide +kernel
 have reached := NorthBound12.north_reached.append first.trace
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 have selected := first.end_subset initialUnique NorthTagFacts12.selected (by decide +kernel) (by decide +kernel)
 have actualInside := List.Subset.trans locks selected.2
 have oldLocks := NorthPrepared12.g_end_subset first i tAt unchanged
 have fixedOld : ∀ small : List Cell, small⊆NorthEvents12.J → endGroup small before=small := by
   intro small h
   exact unchanged small (List.Subset.trans h (by decide +kernel))
 rcases pays with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
 · obtain ⟨result,adjacent,push⟩ := effect_push_data checked effect
   exact False.elim (CageFour12.blocked_impossible actualInside checked effect (block210 i middle.player hero adjacent))
 · obtain ⟨result,adjacent,push⟩ := effect_push_data checked effect
   exact False.elim (CageFour12.blocked_impossible actualInside checked effect (block238 i middle.player hero adjacent))
 · have endingSame := push_effect_singleton soko1_2.initial.holes reached.holes_sublist.subset
     (show pushTargets soko1_2.board 265 .south=[291] by decide +kernel)
     (by decide +kernel) checked effect
   subst ending
   obtain ⟨result,adjacent,push⟩ := effect_push_data checked effect
   have sStage := North265Stage12.north_s212 i middle.player hero adjacent
   have upperSame := unchanged PreCage12.U (by intro c h; exact List.mem_append_left _ h)
   change endGroup CageLedger12.Upper before=CageLedger12.Upper at upperSame
   have tag : endGroup [345] before=[NorthEvents12.current (NorthPrepared12.oldIndex i)] := by
     rw [←old_tag i]
     exact tAt
   have sHere : endGroup [213] before=[212] := by simpa only [sStage] using sAt
   have lower := North265Price23112.first265_lower_231 logged completed shape first checked effect last
     (NorthPrepared12.oldIndex i) fixedOld tag
   omega
 · have endingSame := push_effect_singleton soko1_2.initial.holes reached.holes_sublist.subset
     (show pushTargets soko1_2.board 318 .west=[317] by decide +kernel)
     (by decide +kernel) checked effect
   subst ending
   have lower := North31823112.first318_lower231 logged completed shape first checked effect last
     (NorthPrepared12.oldIndex i) (NorthPrepared12.old_region i hero) oldLocks fixedOld
   omega
 · have endingSame := push_effect_singleton soko1_2.initial.holes reached.holes_sublist.subset
     NorthEvents12.ring_activation (by decide +kernel) checked effect
   subst ending
   have current : PreCage12.northTag i=291 := by
     have all : ∀ i, 291∈PreCage12.northLocks i → PreCage12.northTag i=291 := by decide +kernel
     exact all i sourceMember
   have perm : NorthTagFacts12.selected.Perm L := by decide +kernel
   have groups := endGroup_perm perm before
   have locksL : PreCage12.northLocks i⊆endGroup L before :=
     fun _ h=>groups.mem_iff.mp (locks h)
   have lower:=North29123212.first291_west logged completed shape first checked effect last i hero locksL sourceMember
   omega

#print axioms event_lower231
end Owner1007.NorthMain23112
