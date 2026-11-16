import Owner1007.Quad290Nine12
import Owner1007.North265Price23112
import Owner1007.NorthParityPrice23212
import Owner1007.NorthFirstJ22812
import Owner1007.NorthSNecessary22912
import Owner1007.North265Price23012
import Owner1007.North31823112
import Owner1007.NorthBudgetParity22912
import Owner1007.NorthParityPrice12
namespace Owner1007.NorthFirstJ23012
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12 Owner1007.PreCage12
open Owner1007.NorthTagFacts12 Owner1007.NorthActivation12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential

/-- Actual original firstJ event, obtained without a separate route,
energy, quietness or coverage assumption. -/
abbrev FirstJ := NorthFirstJ22812.FirstJ

theorem after_s {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : 1+pushes≤230)
 {start before0Dirs before0Pushes before0Moves before0 after0Dirs after0Pushes after0Moves after0}
 (shape0 : outcomes=before0++after0)
 (lead : Logged soko1_2.board FirstSplit12.afterN before0Dirs start before0Pushes before0Moves before0)
 (suffix : Logged soko1_2.board start after0Dirs final after0Pushes after0Moves after0)
 (i : Fin 5) (hero0 : start.player∈North21112.region i)
 (inside0 : North21112.locks i⊆endGroup GS before0)
 (s0 : endGroup [213] before0=[211])
 (fixed0 : ∀ small : List Cell, small⊆NorthEvents12.J → endGroup small before0=small)
 (pricedS0 : 2≤ownSlack p [213] before0) : Nonempty (FirstJ final outcomes) := by
 have initialUnique : FirstSplit12.afterN.boulders.Nodup := by decide +kernel
 have gUnique : GS.Nodup := by decide +kernel
 have gSubset : GS⊆FirstSplit12.afterN.boulders := by decide +kernel
 have sNN := suffix.energy_nonnegative Generated.soko1_2_potential_valid (endGroup [213] before0)
 change 0≤energy p (endGroup [213] before0) after0 at sNN
 have sWhole : 2≤energy p [213] outcomes := by
   rw [shape0,TokenAccounting.energy_append]
   omega
 have splitWhole := logged.energy_split initialUnique p NorthBound12.G [213] gUnique gSubset
 change energy p GS outcomes=energy p NorthBound12.G outcomes+energy p [213] outcomes at splitWhole
 have startReached := NorthBound12.north_reached.append lead.trace
 have startGroup := lead.end_subset initialUnique GS gUnique gSubset
 have event := North21112.has_event suffix startReached (endGroup GS before0)
   startGroup.1 startGroup.2 completed hero0 inside0
 obtain ⟨beforeDirs,beforePushes,beforeMoves,before,middle,dir,t,outcome,after,
    afterDirs,afterPushes,afterMoves,j,shape,first,checked,effect,last,hero,locks,pays,unchanged⟩ :=
   event.split_fixed North21112.fixed North21112.fixed_inside North21112.fixed_guard
     startReached startGroup.1 startGroup.2
 let globalBefore : List Outcome := before0++before
 have firstGlobal := lead.append first
 have globalReached := NorthBound12.north_reached.append firstGlobal.trace
 have globalUnique := globalReached.boulders_nodup (by decide +kernel)
 have oldGroup := firstGlobal.end_subset initialUnique GS gUnique gSubset
 have globalShape : outcomes=globalBefore++outcome::after := by
   rw [shape0,shape]
   simp only [globalBefore,List.append_assoc]
 have globalLocks : North21112.locks j⊆endGroup GS globalBefore := by
   simpa only [globalBefore,endGroup_append] using locks
 have sGlobal : endGroup [213] globalBefore=[211] := by
   rw [show globalBefore=before0++before from rfl,endGroup_append,s0]
   exact unchanged [211] (by decide +kernel)
 have fixedGlobal : ∀ small : List Cell, small⊆NorthEvents12.J →
     endGroup small globalBefore=small := by
   intro small h
   rw [show globalBefore=before0++before from rfl,endGroup_append,fixed0 small h]
   exact unchanged small (List.Subset.trans h (by decide +kernel))
 have split := firstGlobal.end_split initialUnique NorthBound12.G [213] gUnique gSubset
 change (endGroup NorthBound12.G globalBefore ++ endGroup [213] globalBefore).Perm
   (endGroup GS globalBefore) at split
 rw [sGlobal] at split
 have oldLocks : NorthEvents12.locks j⊆endGroup NorthBound12.G globalBefore := by
   intro c found
   have member := split.mem_iff.mpr (globalLocks (North21112.old_locks j found))
   rcases List.mem_append.mp member with own|other
   · exact own
   · have same : c=211 := List.mem_singleton.mp other
     exact False.elim (North211GEight22812.old_away j (same ▸ found))
 have prefixS : 2≤ownSlack p [213] globalBefore := by
   have nn:=first.ownSlack_nonnegative Generated.soko1_2_potential_valid (endGroup [213] before0)
   change 0≤ownSlack p (endGroup [213] before0) before at nn
   rw[show globalBefore=before0++before from rfl,ownSlack_append]
   omega
 have prefixMono:=firstGlobal.ownSlack_mono Generated.soko1_2_potential_valid initialUnique
   [213] GS (by decide +kernel) gUnique (by decide +kernel) gSubset (by decide +kernel)
 change ownSlack p [213] globalBefore≤ownSlack p GS globalBefore at prefixMono
 have prefixGS:2≤ownSlack p GS globalBefore:=by omega
 cases outcome with
 | walk target => exact False.elim pays
 | push source ending =>
   obtain ⟨owner,paid⟩ := pays
   have ownerGlobal : source∈endGroup GS globalBefore := by
     simpa only [globalBefore,endGroup_append] using owner
   rcases paid with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
   · have endingSame := push_effect_singleton soko1_2.initial.holes globalReached.holes_sublist.subset
       (show pushTargets soko1_2.board 210 .south=[236] by decide +kernel)
       (by decide +kernel) checked effect
     subst ending
     exact ⟨{
       kind := 0,
       middle := middle,
       actor := t,
       beforeDirs := before0Dirs ++ beforeDirs,
       beforePushes := before0Pushes + beforePushes,
       beforeMoves := before0Moves + beforeMoves,
       before := globalBefore,
       afterDirs := afterDirs,
       afterPushes := afterPushes,
       afterMoves := afterMoves,
       after := after,
       phase := j,
       shape := globalShape,
       first := firstGlobal,
       checked := checked,
       effect := effect,
       last := last,
       locks := oldLocks,
       fixedBefore := fixedGlobal,
       sAt := sGlobal }⟩
   · have endingSame := push_effect_singleton soko1_2.initial.holes globalReached.holes_sublist.subset
       (show pushTargets soko1_2.board 238 .south=[264] by decide +kernel)
       (by decide +kernel) checked effect
     subst ending
     exact ⟨{
       kind := 1,
       middle := middle,
       actor := t,
       beforeDirs := before0Dirs ++ beforeDirs,
       beforePushes := before0Pushes + beforePushes,
       beforeMoves := before0Moves + beforeMoves,
       before := globalBefore,
       afterDirs := afterDirs,
       afterPushes := afterPushes,
       afterMoves := afterMoves,
       after := after,
       phase := j,
       shape := globalShape,
       first := firstGlobal,
       checked := checked,
       effect := effect,
       last := last,
       locks := oldLocks,
       fixedBefore := fixedGlobal,
       sAt := sGlobal }⟩
   · have endingSame := push_effect_singleton soko1_2.initial.holes globalReached.holes_sublist.subset
       (show pushTargets soko1_2.board 265 .south=[291] by decide +kernel)
       (by decide +kernel) checked effect
     subst ending
     have tag := NorthBudgetParity22912.current_tag firstGlobal j oldLocks fixedGlobal
     have lower := North265Price23112.first265_lower_231 logged completed globalShape firstGlobal
       checked effect last j fixedGlobal tag
     omega
   · have endingSame := push_effect_singleton soko1_2.initial.holes globalReached.holes_sublist.subset
       (show pushTargets soko1_2.board 318 .west=[317] by decide +kernel)
       (by decide +kernel) checked effect
     subst ending
     have lower := North31823112.first318_lower231 logged completed globalShape firstGlobal
       checked effect last j (North21112.old_region j hero) oldLocks fixedGlobal
     omega
   · have endingSame := push_effect_singleton soko1_2.initial.holes globalReached.holes_sublist.subset
       NorthEvents12.ring_activation (by decide +kernel) checked effect
     subst ending
     obtain ⟨result,adjacent,push⟩ := effect_push_data checked effect
     have member := North211GEight22812.ring_member j middle.player hero adjacent
     have nextActual := step_boulders_nodup _ _ _ _ globalUnique checked
     have nextUnique := GhostSubset.update_unique middle t (.push 291 (.stay 290)) effect nextActual
       (endGroup GS globalBefore) oldGroup.1 oldGroup.2
     have nextSubset := GhostSubset.update_subset middle t (.push 291 (.stay 290)) effect
       (endGroup GS globalBefore) oldGroup.1 oldGroup.2
     have kept := CageFour12.shifted_inside (North21112.unique j) globalLocks ownerGlobal
       (North21112.quad_activation j member)
     have nextHero : t.state.player∈Quad29012.region 0 := by
       rw [matches_hero middle t (.push 291 (.stay 290)) effect]
       exact North21112.quad_hero
     have nextReached := globalReached.append (Trace.cons checked (Trace.nil t.state))
     have later := Quad290Nine12.energy_nine last nextReached
       (update (endGroup GS globalBefore) (.push 291 (.stay 290))) nextUnique nextSubset completed nextHero kept
     have nn := firstGlobal.ownSlack_nonnegative Generated.soko1_2_potential_valid GS
     have one : slack p (.push 291 (.stay 290))=2 := by decide +kernel
     change 9≤energy p (update (endGroup GS globalBefore) (.push 291 (.stay 290))) after at later
     change 0≤ownSlack p GS globalBefore at nn
     have lower : 13≤energy p GS outcomes := by
       rw [globalShape,energy_at_split]
       simp only [projectedOutcome,if_pos ownerGlobal,one]
       omega
     have upper := RightEnergy12.raw_group_energy logged NorthBound12.north_reached PreCage12.U
       (by decide +kernel) (by decide +kernel) completed
     have bonus : RightEnergy12.cert.bonus FirstSplit12.afterN.player (PatternCorrection.project PreCage12.U)=2 := by decide +kernel
     rw [bonus] at upper
     change 2≤energy p PreCage12.U outcomes at upper
     have leftSplit := logged.energy_split initialUnique p PreCage12.U GS (by decide +kernel) (by decide +kernel)
     change energy p NorthPriceBalance12.Left outcomes=energy p PreCage12.U outcomes+energy p GS outcomes at leftSplit
     have lowerLeft : 15≤energy p NorthPriceBalance12.Left outcomes := by omega
     have count := NorthParityPrice23212.fifteen_implies_232 logged completed lowerLeft
     omega

#print axioms after_s
end Owner1007.NorthFirstJ23012
