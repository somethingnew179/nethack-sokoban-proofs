import Owner1007.NorthTight22812
import Owner1007.North265Nine12
namespace Owner1007.NorthFirstJ22812
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12 Owner1007.PreCage12
open Owner1007.NorthTagFacts12 Owner1007.NorthActivation12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential

/-- Actual original firstJ event, obtained without a separate route,
energy, quietness or coverage assumption. -/
structure FirstJ (final : State) (outcomes : List Outcome) where
 kind : Fin 2
 middle : State
 actor : Transition
 beforeDirs : List Dir
 beforePushes : Nat
 beforeMoves : Nat
 before : List Outcome
 afterDirs : List Dir
 afterPushes : Nat
 afterMoves : Nat
 after : List Outcome
 phase : Fin 5
 shape : outcomes=before++AfterJBound12.headOutcome kind::after
 first : Logged soko1_2.board FirstSplit12.afterN beforeDirs middle beforePushes beforeMoves before
 checked : step soko1_2.board middle .south=some actor
 effect : Matches middle actor (AfterJBound12.headOutcome kind)
 last : Logged soko1_2.board actor.state afterDirs final afterPushes afterMoves after
 locks : NorthEvents12.locks phase⊆endGroup NorthBound12.G before
 fixedBefore : ∀small : List Cell,small⊆NorthEvents12.J→endGroup small before=small
 sAt : endGroup [213] before=[211]

theorem after_s {dirs final pushes moves outcomes}
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
     have alternatives := North265Nine12.first265_nine_or_survivor logged completed globalShape firstGlobal
       checked effect last j oldLocks
     have ledgers := NorthTight22812.canonical_ledgers logged completed cheap
     have eight := ledgers.2.2.1
     change energy p NorthBound12.G outcomes=8 at eight
     have leftGone := ledgers.2.2.2.2.2.1
     have mono := logged.end_mono initialUnique NorthBound12.G NorthPriceBalance12.Left
       (by decide +kernel) (by decide +kernel) (by decide +kernel)
     rw [leftGone] at mono
     have gone : endGroup NorthBound12.G outcomes=[] :=
       List.eq_nil_iff_forall_not_mem.mpr (by intro c member;simpa using mono member)
     rcases alternatives with nine|survives
     · change 9≤energy p NorthBound12.G outcomes at nine
       omega
     · exact False.elim (survives.2 gone)
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

theorem canonical {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : 1+pushes≤228) : Nonempty (FirstJ final outcomes) := by
 obtain ⟨bd,bp,bm,before,middle,t,after,ad,ap,am,i,shape,first,checked,effect,last,hero,locks,sAt,tAt,unchanged⟩ :=
   NorthSNecessary22812.necessary_first_s logged completed cheap
 have reached := NorthBound12.north_reached.append first.trace
 have physical := first.end_subset (by decide +kernel) selected (by decide +kernel) (by decide +kernel)
 obtain ⟨_,adjacent,_⟩ := effect_push_data checked effect
 have at212 : northS i=212 := by
   rcases NorthActivation12.pre_s_heads i middle.player hero .west (Geometry.all_directions .west)
     212 (by decide +kernel) (by decide +kernel) adjacent with blocked|actual
   · exact False.elim (CageFour12.blocked_impossible (List.Subset.trans locks physical.2) checked effect blocked)
   · exact actual.2.2
 have initialUnique : FirstSplit12.afterN.boulders.Nodup := by decide +kernel
 let before1 : List Outcome := before++[.push 212 (.stay 211)]
 have lead1 := first.append (Logged.cons checked effect (Logged.nil t.state))
 have shape1 : outcomes=before1++after := by
   rw [shape]
   simp only [before1,List.append_assoc,List.cons_append,List.nil_append]
 have oldG := NorthPrepared12.g_end_subset first i tAt unchanged
 have gsUnique : NorthActivation12.GS.Nodup := by decide +kernel
 have gsSubset : NorthActivation12.GS⊆FirstSplit12.afterN.boulders := by decide +kernel
 have split := first.end_split initialUnique NorthBound12.G [213] gsUnique gsSubset
 change (endGroup NorthBound12.G before++endGroup [213] before).Perm
   (endGroup NorthActivation12.GS before) at split
 rw [sAt] at split
 have preInside : NorthEvents12.locks (NorthPrepared12.oldIndex i)++[212]⊆
     endGroup NorthActivation12.GS before := by
   intro c found
   apply split.mem_iff.mp
   rcases List.mem_append.mp found with old|same
   · exact List.mem_append_left _ (oldG old)
   · exact List.mem_append_right _ same
 have ownerGS : 212∈endGroup NorthActivation12.GS before :=
   preInside (List.mem_append_right _ (by simp))
 have preUnique : (NorthEvents12.locks (NorthPrepared12.oldIndex i)++[212]).Nodup := by
   have all : ∀ j, (NorthEvents12.locks j++[212]).Nodup := by decide +kernel
   exact all _
 have shift : North21112.locks (NorthPrepared12.oldIndex i)⊆
     211::(NorthEvents12.locks (NorthPrepared12.oldIndex i)++[212]).erase 212 := by
   have all : ∀ j, North21112.locks j⊆211::(NorthEvents12.locks j++[212]).erase 212 := by decide +kernel
   exact all _
 have kept := CageFour12.shifted_inside preUnique preInside ownerGS shift
 have inside1 : North21112.locks (NorthPrepared12.oldIndex i)⊆endGroup NorthActivation12.GS before1 := by
   simpa only [before1,endGroup_append,endGroup] using kept
 have s1 : endGroup [213] before1=[211] := by
   rw [show before1=before++[.push 212 (.stay 211)] from rfl,endGroup_append,sAt]
   decide +kernel
 have fixed1 : ∀ small : List Cell, small⊆NorthEvents12.J → endGroup small before1=small := by
   intro small h
   rw [show before1=before++[.push 212 (.stay 211)] from rfl,endGroup_append,
     unchanged small (List.Subset.trans h (by decide +kernel))]
   have absent : (212:Cell)∉small := fun found=>(show (212:Cell)∉NorthEvents12.J by decide +kernel) (h found)
   simp only [endGroup,update,move,if_neg absent]
 have priced1 : 2≤ownSlack p [213] before1 := by
   have nn := first.ownSlack_nonnegative Generated.soko1_2_potential_valid [213]
   change 0≤ownSlack p [213] before at nn
   rw [show before1=before++[.push 212 (.stay 211)] from rfl,ownSlack_append,sAt]
   have one : ownSlack p [212] [.push 212 (.stay 211)]=2 := by decide +kernel
   rw [one]
   omega
 have hero1 : t.state.player∈North21112.region (NorthPrepared12.oldIndex i) := by
   rw [matches_hero middle t (.push 212 (.stay 211)) effect]
   exact (North21112.start_activation i at212).2
 exact after_s logged completed cheap shape1 lead1 last
   (NorthPrepared12.oldIndex i) hero1 inside1 s1 fixed1 priced1
#print axioms after_s
#print axioms canonical
end Owner1007.NorthFirstJ22812
