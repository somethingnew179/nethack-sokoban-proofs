import Owner1007.North211Priced12
import Owner1007.NorthJSurvival12
import Owner1007.NorthPriceBalance12
import Owner1007.NorthActivation12
import Owner1007.NorthJSeven12
import Owner1007.North265Count12
import Owner1007.North318BoundPlus12
namespace Owner1007.North211Tight22812
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
open Owner1007.NorthActivation12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
theorem ring_member : ∀ i, ∀ hero∈North21112.region i,
 advance soko1_2.board hero .west=some 291 → 291∈North21112.locks i := by decide +kernel
theorem old_away : ∀ i, (211:Cell)∉NorthEvents12.locks i := by decide +kernel

theorem upper_le_two {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : 1+pushes≤228)
 {start before0Dirs before0Pushes before0Moves before0 after0Dirs after0Pushes after0Moves after0}
 (shape0 : outcomes=before0++after0)
 (lead : Logged soko1_2.board FirstSplit12.afterN before0Dirs start before0Pushes before0Moves before0)
 (suffix : Logged soko1_2.board start after0Dirs final after0Pushes after0Moves after0)
 (i : Fin 5) (hero0 : start.player∈North21112.region i)
 (inside0 : North21112.locks i⊆endGroup GS before0)
 (s0 : endGroup [213] before0=[211])
 (fixed0 : ∀ small : List Cell, small⊆NorthEvents12.J → endGroup small before0=small)
 (pricedS0 : 2≤ownSlack p [213] before0) : energy p PreCage12.U outcomes≤2 := by
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
 have leftSplit := logged.energy_split initialUnique p PreCage12.U GS (by decide +kernel) (by decide +kernel)
 change energy p NorthPriceBalance12.Left outcomes=energy p PreCage12.U outcomes+energy p GS outcomes at leftSplit
 have total := NorthPriceBalance12.total logged completed
 change energy p NorthPriceBalance12.Left outcomes+energy p Final222.R outcomes=Int.ofNat (1+pushes)-212 at total
 simp only [Int.ofNat_eq_natCast] at total
 have closeG (cases : 8≤energy p NorthBound12.G outcomes ∨
     (7≤energy p NorthBound12.G outcomes ∧ endGroup NorthBound12.G outcomes≠[])) :
     energy p PreCage12.U outcomes≤2 := by
   rcases cases with large|⟨seven,survives⟩
   · have right := NorthPriceBalance12.right_four logged completed
     change 4≤energy p Final222.R outcomes at right
     omega
   · have mono := logged.end_mono initialUnique NorthBound12.G NorthPriceBalance12.Left
       (by decide +kernel) (by decide +kernel) (by decide +kernel)
     have alive : endGroup NorthPriceBalance12.Left outcomes≠[] := by
       intro empty
       exact survives (List.eq_nil_iff_forall_not_mem.mpr (by
         intro c member
         simpa only [empty,List.not_mem_nil] using mono member))
     have right := NorthLeftSurvival12.right_five logged completed alive
     change 5≤energy p Final222.R outcomes at right
     omega
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
     exact False.elim (old_away j (same ▸ found))
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
     have lower := NorthJSurvival12.firstJ_eight_or_survivor logged completed 0 globalShape firstGlobal
       checked effect last j oldLocks fixedGlobal
     exact closeG lower
   · have endingSame := push_effect_singleton soko1_2.initial.holes globalReached.holes_sublist.subset
       (show pushTargets soko1_2.board 238 .south=[264] by decide +kernel)
       (by decide +kernel) checked effect
     subst ending
     have lower := NorthJSurvival12.firstJ_eight_or_survivor logged completed 1 globalShape firstGlobal
       checked effect last j oldLocks fixedGlobal
     exact closeG lower
   · have endingSame := push_effect_singleton soko1_2.initial.holes globalReached.holes_sublist.subset
       (show pushTargets soko1_2.board 265 .south=[291] by decide +kernel)
       (by decide +kernel) checked effect
     subst ending
     have lower := North265Eight12.first265_eight logged completed globalShape firstGlobal
       checked effect last j oldLocks
     change 8≤energy p NorthBound12.G outcomes at lower
     exact closeG (Or.inl lower)
   · have endingSame := push_effect_singleton soko1_2.initial.holes globalReached.holes_sublist.subset
       (show pushTargets soko1_2.board 318 .west=[317] by decide +kernel)
       (by decide +kernel) checked effect
     subst ending
     have lower := North318BoundPlus12.first318_lower229 logged completed globalShape firstGlobal
       checked effect last j (North21112.old_region j hero) oldLocks fixedGlobal
     omega
   · have endingSame := push_effect_singleton soko1_2.initial.holes globalReached.holes_sublist.subset
       NorthEvents12.ring_activation (by decide +kernel) checked effect
     subst ending
     obtain ⟨result,adjacent,push⟩ := effect_push_data checked effect
     have member := ring_member j middle.player hero adjacent
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
     have later := Quad29012.energy_seven last nextReached
       (update (endGroup GS globalBefore) (.push 291 (.stay 290))) nextUnique nextSubset completed nextHero kept
     have nn := firstGlobal.ownSlack_nonnegative Generated.soko1_2_potential_valid GS
     have one : slack p (.push 291 (.stay 290))=2 := by decide +kernel
     change 7≤energy p (update (endGroup GS globalBefore) (.push 291 (.stay 290))) after at later
     change 0≤ownSlack p GS globalBefore at nn
     have lower : 11≤energy p GS outcomes := by
       rw [globalShape,energy_at_split]
       simp only [projectedOutcome,if_pos ownerGlobal,one]
       omega
     have count := canonical_joint_bound logged completed 11 lower
     omega
theorem upper_two {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : 1+pushes≤228)
 {start before0Dirs before0Pushes before0Moves before0 after0Dirs after0Pushes after0Moves after0}
 (shape0 : outcomes=before0++after0)
 (lead : Logged soko1_2.board FirstSplit12.afterN before0Dirs start before0Pushes before0Moves before0)
 (suffix : Logged soko1_2.board start after0Dirs final after0Pushes after0Moves after0)
 (i : Fin 5) (hero0 : start.player∈North21112.region i)
 (inside0 : North21112.locks i⊆endGroup GS before0)
 (s0 : endGroup [213] before0=[211])
 (fixed0 : ∀ small : List Cell, small⊆NorthEvents12.J → endGroup small before0=small)
 (pricedS0 : 2≤ownSlack p [213] before0) : energy p PreCage12.U outcomes=2 := by
 have upper := upper_le_two logged completed cheap shape0 lead suffix i hero0 inside0 s0 fixed0 pricedS0
 have whole := NorthWrap12.canonical_north logged
 have lower := Final222.upper_energy_two whole completed
 have same := (NorthWrap12.energy_north Final222.U outcomes).trans
   (congrArg (fun group=>energy p group outcomes)
     (show update Final222.U (.push 371 (.stay 345))=Final222.U by decide +kernel))
 change 2≤energy p Final222.U (.walk 397::.push 371 (.stay 345)::outcomes) at lower
 rw [same] at lower
 change 2≤energy p PreCage12.U outcomes at lower
 omega
#print axioms upper_two
#print axioms upper_le_two
end Owner1007.North211Tight22812

