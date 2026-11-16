import Owner1007.RingUpperReserveEight12
import Owner1007.North18712
import Owner1007.North211Priced12
import Owner1007.NorthLeftBudget22612
import Owner1007.RingUpperBound12
import Owner1007.NorthJSeven12
import Owner1007.North265Nine12
import Owner1007.North318BoundPlus12
namespace Owner1007.North187Strong22612
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
open Owner1007.NorthActivation12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
abbrev L := NorthLeftBudget22612.Left
def UA : List Cell := [161,108,158,159,186]
theorem ring_member : ∀ i, ∀ hero∈North18712.region i,
 advance soko1_2.board hero .west=some 291 → 291∈North18712.locks i := by decide +kernel
theorem old_away : ∀ i, (212:Cell)∉NorthEvents12.locks i := by decide +kernel
theorem gs_inside : ∀ i, NorthEvents12.locks i++[212] ⊆ North18712.locks i := by decide +kernel
theorem gs_away : ∀ i, ∀ c∈NorthEvents12.locks i++[212], c∉UA := by decide +kernel
theorem ring_shift : ∀ i, 291∈North18712.locks i →
 RingUpper12.locks 0 ⊆ 290::(North18712.locks i).erase 291 := by decide +kernel
theorem s_shift : ∀ i, North21112.locks i ⊆ 211::(NorthEvents12.locks i++[212]).erase 212 := by decide +kernel

theorem block210 : ∀ i, ∀ hero∈North18712.region i,
 advance soko1_2.board hero .south=some 210 → BlockedPush soko1_2.board (North18712.locks i) 210 .south := by decide +kernel
theorem block238 : ∀ i, ∀ hero∈North18712.region i,
 advance soko1_2.board hero .south=some 238 → BlockedPush soko1_2.board (North18712.locks i) 238 .south := by decide +kernel

theorem impossible {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : 1+pushes≤226)
 {start before0Dirs before0Pushes before0Moves before0 after0Dirs after0Pushes after0Moves after0}
 (shape0 : outcomes=before0++after0)
 (lead : Logged soko1_2.board FirstSplit12.afterN before0Dirs start before0Pushes before0Moves before0)
 (suffix : Logged soko1_2.board start after0Dirs final after0Pushes after0Moves after0)
 (i : Fin 5) (hero0 : start.player∈North18712.region i)
 (inside0 : North18712.locks i⊆endGroup L before0)
 (u0 : endGroup PreCage12.U before0=UA)
 (s0 : endGroup [213] before0=[212])
 (fixed0 : ∀ small : List Cell, small⊆NorthEvents12.J → endGroup small before0=small)
 (priced0 : 2≤ownSlack p L before0) : False := by
 have initialUnique : FirstSplit12.afterN.boulders.Nodup := by decide +kernel
 have lUnique : L.Nodup := by decide +kernel
 have lSubset : L⊆FirstSplit12.afterN.boulders := by decide +kernel
 have gsUnique : GS.Nodup := by decide +kernel
 have gsSubset : GS⊆FirstSplit12.afterN.boulders := by decide +kernel
 have startReached := NorthBound12.north_reached.append lead.trace
 have startGroup := lead.end_subset initialUnique L lUnique lSubset
 have event := North18712.has_event suffix startReached (endGroup L before0)
   startGroup.1 startGroup.2 completed hero0 inside0
 obtain ⟨beforeDirs,beforePushes,beforeMoves,before,middle,dir,t,outcome,after,
    afterDirs,afterPushes,afterMoves,j,shape,first,checked,effect,last,hero,locks,pays,unchanged⟩ :=
   event.split_fixed North18712.fixed North18712.fixed_inside North18712.fixed_guard
     startReached startGroup.1 startGroup.2
 let globalBefore : List Outcome := before0++before
 have firstGlobal := lead.append first
 have globalReached := NorthBound12.north_reached.append firstGlobal.trace
 have globalUnique := globalReached.boulders_nodup (by decide +kernel)
 have oldGroup := firstGlobal.end_subset initialUnique L lUnique lSubset
 have globalShape : outcomes=globalBefore++outcome::after := by
   rw [shape0,shape]
   simp only [globalBefore,List.append_assoc]
 have globalLocks : North18712.locks j⊆endGroup L globalBefore := by
   simpa only [globalBefore,endGroup_append] using locks
 have sGlobal : endGroup [213] globalBefore=[212] := by
   rw [show globalBefore=before0++before from rfl,endGroup_append,s0]
   exact unchanged [212] (by decide +kernel)
 have uGlobal : endGroup PreCage12.U globalBefore=UA := by
   rw [show globalBefore=before0++before from rfl,endGroup_append,u0]
   exact unchanged UA (by decide +kernel)
 have fixedGlobal : ∀ small : List Cell, small⊆NorthEvents12.J →
     endGroup small globalBefore=small := by
   intro small h
   rw [show globalBefore=before0++before from rfl,endGroup_append,fixed0 small h]
   exact unchanged small (List.Subset.trans h (by decide +kernel))
 have prefixPrice : 2≤ownSlack p L globalBefore := by
   have nn := first.ownSlack_nonnegative Generated.soko1_2_potential_valid (endGroup L before0)
   change 0≤ownSlack p (endGroup L before0) before at nn
   rw [show globalBefore=before0++before from rfl,ownSlack_append]
   omega
 have splitU := firstGlobal.end_split initialUnique PreCage12.U GS lUnique lSubset
 change (endGroup PreCage12.U globalBefore++endGroup GS globalBefore).Perm
   (endGroup L globalBefore) at splitU
 rw [uGlobal] at splitU
 have gsInside : NorthEvents12.locks j++[212]⊆endGroup GS globalBefore := by
   intro c found
   have member := splitU.mem_iff.mpr (globalLocks (gs_inside j found))
   rcases List.mem_append.mp member with own|other
   · exact False.elim (gs_away j c found own)
   · exact other
 have splitGS := firstGlobal.end_split initialUnique NorthBound12.G [213] gsUnique gsSubset
 change (endGroup NorthBound12.G globalBefore++endGroup [213] globalBefore).Perm
   (endGroup GS globalBefore) at splitGS
 rw [sGlobal] at splitGS
 have oldLocks : NorthEvents12.locks j⊆endGroup NorthBound12.G globalBefore := by
   intro c found
   have member := splitGS.mem_iff.mpr (gsInside (List.mem_append_left _ found))
   rcases List.mem_append.mp member with own|other
   · exact own
   · have same : c=212 := List.mem_singleton.mp other
     exact False.elim (old_away j (same ▸ found))
 have leftBudget := NorthLeftBudget22612.budget logged completed cheap
 change energy p L outcomes≤10 at leftBudget
 cases outcome with
 | walk target => exact False.elim pays
 | push source ending =>
   obtain ⟨owner,paid⟩ := pays
   have ownerGlobal : source∈endGroup L globalBefore := by
     simpa only [globalBefore,endGroup_append] using owner
   have nextActual := step_boulders_nodup _ _ _ _ globalUnique checked
   have nextUnique := GhostSubset.update_unique middle t (.push source ending) effect nextActual
     (endGroup L globalBefore) oldGroup.1 oldGroup.2
   have nextSubset := GhostSubset.update_subset middle t (.push source ending) effect
     (endGroup L globalBefore) oldGroup.1 oldGroup.2
   have nextReached := globalReached.append (Trace.cons checked (Trace.nil t.state))
   have reserve (a b : Int) (one : a≤slack p (.push source ending))
       (later : b≤energy p (update (endGroup L globalBefore) (.push source ending)) after) :
       2+a+b≤energy p L outcomes := by
     rw [globalShape,energy_at_split]
     simp only [projectedOutcome,if_pos ownerGlobal]
     omega
   rcases paid with paid|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
   · rcases paid with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
     · have endingSame := push_effect_singleton soko1_2.initial.holes globalReached.holes_sublist.subset
         (show pushTargets soko1_2.board 210 .south=[236] by decide +kernel)
         (by decide +kernel) checked effect
       subst ending
       obtain ⟨result,adjacent,push⟩ := effect_push_data checked effect
       exact CageFour12.blocked_impossible (List.Subset.trans globalLocks oldGroup.2)
         checked effect (block210 j middle.player hero adjacent)
     · have endingSame := push_effect_singleton soko1_2.initial.holes globalReached.holes_sublist.subset
         (show pushTargets soko1_2.board 238 .south=[264] by decide +kernel)
         (by decide +kernel) checked effect
       subst ending
       obtain ⟨result,adjacent,push⟩ := effect_push_data checked effect
       exact CageFour12.blocked_impossible (List.Subset.trans globalLocks oldGroup.2)
         checked effect (block238 j middle.player hero adjacent)
     · have endingSame := push_effect_singleton soko1_2.initial.holes globalReached.holes_sublist.subset
         (show pushTargets soko1_2.board 265 .south=[291] by decide +kernel)
         (by decide +kernel) checked effect
       subst ending
       have lower := North265Nine12.first265_lower227 logged completed globalShape firstGlobal
         checked effect last j oldLocks
       omega
     · have endingSame := push_effect_singleton soko1_2.initial.holes globalReached.holes_sublist.subset
         (show pushTargets soko1_2.board 318 .west=[317] by decide +kernel)
         (by decide +kernel) checked effect
       subst ending
       have lower := North318BoundPlus12.first318_lower229 logged completed globalShape firstGlobal
         checked effect last j (North18712.old_region j hero) oldLocks fixedGlobal
       omega
     · have endingSame := push_effect_singleton soko1_2.initial.holes globalReached.holes_sublist.subset
         NorthEvents12.ring_activation (by decide +kernel) checked effect
       subst ending
       obtain ⟨result,adjacent,push⟩ := effect_push_data checked effect
       have member := ring_member j middle.player hero adjacent
       have kept := CageFour12.shifted_inside (North18712.unique j) globalLocks ownerGlobal
         (ring_shift j member)
       have nextHero : t.state.player∈RingUpper12.region 0 := by
         rw [matches_hero middle t (.push 291 (.stay 290)) effect]
         decide +kernel
       have later := RingUpperReserveEight12.energy_eight
         last nextReached (update (endGroup L globalBefore) (.push 291 (.stay 290)))
         nextUnique nextSubset completed nextHero kept
       change 8≤energy p (update (endGroup L globalBefore) (.push 291 (.stay 290))) after at later
       have bound := reserve 2 8 (by decide +kernel) later
       omega
   · have endingSame := push_effect_singleton soko1_2.initial.holes globalReached.holes_sublist.subset
       (show pushTargets soko1_2.board 186 .west=[185] by decide +kernel)
       (by decide +kernel) checked effect
     subst ending
     have kept := CageFour12.shifted_inside (North18712.unique j) globalLocks ownerGlobal
       (North18712.gate_activation j)
     have nextHero : t.state.player∈PriceTrap12Gate.region 0 := by
       rw [matches_hero middle t (.push 186 (.stay 185)) effect]
       exact North18712.gate_hero
     have later := CageLedger12.gate_owned_nineteen last nextReached
       (update (endGroup L globalBefore) (.push 186 (.stay 185))) nextUnique nextSubset nextHero kept
     change 19≤energy p (update (endGroup L globalBefore) (.push 186 (.stay 185))) after at later
     have bound := reserve 2 19 (by decide +kernel) later
     omega
   · have endingSame := push_effect_singleton soko1_2.initial.holes globalReached.holes_sublist.subset
       (show pushTargets soko1_2.board 161 .north=[135] by decide +kernel)
       (by decide +kernel) checked effect
     subst ending
     have ownerU : (161:Cell)∈endGroup PreCage12.U globalBefore := by rw [uGlobal]; decide +kernel
     have upper := event_energy_le Generated.soko1_2_potential_valid PreCage12.U firstGlobal last (.push 161 (.stay 135))
     change slack p (projectedOutcome (endGroup PreCage12.U globalBefore) (.push 161 (.stay 135)))≤
       energy p PreCage12.U (globalBefore++(.push 161 (.stay 135))::after) at upper
     simp only [projectedOutcome,if_pos ownerU] at upper
     rw [←globalShape] at upper
     have headPrice : slack p (.push 161 (.stay 135))=8 := by decide +kernel
     rw [headPrice] at upper
     have gThree : 3≤energy p NorthBound12.G outcomes := by
       rcases NorthBound12.g_cases logged completed with four|three
       · change 4≤energy p NorthBound12.G outcomes at four
         omega
       · exact three.1
     have joint := TwoReserves12.add_le_energy logged Generated.soko1_2_potential_valid initialUnique
       PreCage12.U NorthBound12.G L (by decide +kernel) lUnique lSubset (by decide +kernel)
     change energy p PreCage12.U outcomes+energy p NorthBound12.G outcomes≤energy p L outcomes at joint
     omega
   · have endingSame := push_effect_singleton soko1_2.initial.holes globalReached.holes_sublist.subset
       (show pushTargets soko1_2.board 212 .west=[211] by decide +kernel)
       (by decide +kernel) checked effect
     subst ending
     let before1 : List Outcome := globalBefore++[.push 212 (.stay 211)]
     have lead1 := firstGlobal.append (Logged.cons checked effect (Logged.nil t.state))
     have shape1 : outcomes=before1++after := by
       rw [globalShape]
       simp only [before1,List.append_assoc,List.cons_append,List.nil_append]
     have ownerGS : 212∈endGroup GS globalBefore := gsInside (List.mem_append_right _ (by simp))
     have preUnique : (NorthEvents12.locks j++[212]).Nodup := by
       have all : ∀ j, (NorthEvents12.locks j++[212]).Nodup := by decide +kernel
       exact all j
     have newInside := CageFour12.shifted_inside preUnique gsInside ownerGS (s_shift j)
     have gsAfter : North21112.locks j⊆endGroup GS before1 := by
       simpa only [before1,endGroup_append,endGroup] using newInside
     have sAfter : endGroup [213] before1=[211] := by
       rw [show before1=globalBefore++[.push 212 (.stay 211)] from rfl,endGroup_append,sGlobal]
       simp only [endGroup,update,move,List.mem_cons,List.not_mem_nil,or_false,if_true,post,List.erase_cons_head]
     have fixedAfter : ∀ small : List Cell, small⊆NorthEvents12.J → endGroup small before1=small := by
       intro small h
       rw [show before1=globalBefore++[.push 212 (.stay 211)] from rfl,endGroup_append,fixedGlobal small h]
       have absent : (212:Cell)∉small := fun found=>(show (212:Cell)∉NorthEvents12.J by decide +kernel) (h found)
       simp only [endGroup,update,move,if_neg absent]
     have nextHero : t.state.player∈North21112.region j := by
       rw [matches_hero middle t (.push 212 (.stay 211)) effect]
       exact (North18712.s_activation j).2
     have pricedSAfter : 2≤ownSlack p [213] before1 := by
       have nn := firstGlobal.ownSlack_nonnegative Generated.soko1_2_potential_valid [213]
       change 0≤ownSlack p [213] globalBefore at nn
       rw [show before1=globalBefore++[.push 212 (.stay 211)] from rfl,ownSlack_append,sGlobal]
       have single : ownSlack p [212] [.push 212 (.stay 211)]=2 := by decide +kernel
       rw [single]
       omega
     exact North211Priced12.impossible logged completed (by omega) shape1 lead1 last j nextHero
       gsAfter sAfter fixedAfter pricedSAfter
#print axioms impossible
end Owner1007.North187Strong22612
