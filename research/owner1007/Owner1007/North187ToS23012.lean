import Owner1007.North187Strong22912
import Owner1007.North265Price23112
import Owner1007.NorthParityPrice23212
import Owner1007.RingUpperElevenStrong12
namespace Owner1007.North187ToS23012
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
open Owner1007.NorthActivation12
open Owner1007.North187Strong22912 (L UA ring_member old_away gs_inside gs_away ring_shift s_shift block210 block238)
abbrev p:=Generated.soko1_2Potential
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
structure Stage (final:State) (outcomes:List Outcome) where
 state:State
 beforeDirs:List Dir
 beforePushes:Nat
 beforeMoves:Nat
 before:List Outcome
 afterDirs:List Dir
 afterPushes:Nat
 afterMoves:Nat
 after:List Outcome
 shape:outcomes=before++after
 first:Logged soko1_2.board FirstSplit12.afterN beforeDirs state beforePushes beforeMoves before
 last:Logged soko1_2.board state afterDirs final afterPushes afterMoves after
 phase:Fin 5
 hero:state.player∈North21112.region phase
 inside:North21112.locks phase⊆endGroup NorthActivation12.GS before
 sAt:endGroup [213] before=[211]
 fixed:∀small:List Cell,small⊆NorthEvents12.J→endGroup small before=small
 paid:2≤ownSlack Generated.soko1_2Potential [213] before
theorem to_s211 {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : 1+pushes≤230)
 {start before0Dirs before0Pushes before0Moves before0 after0Dirs after0Pushes after0Moves after0}
 (shape0 : outcomes=before0++after0)
 (lead : Logged soko1_2.board FirstSplit12.afterN before0Dirs start before0Pushes before0Moves before0)
 (suffix : Logged soko1_2.board start after0Dirs final after0Pushes after0Moves after0)
 (i : Fin 5) (hero0 : start.player∈North18712.region i)
 (inside0 : North18712.locks i⊆endGroup L before0)
 (u0 : endGroup PreCage12.U before0=UA)
 (s0 : endGroup [213] before0=[212])
 (fixed0 : ∀ small : List Cell, small⊆NorthEvents12.J → endGroup small before0=small)
 (priced0 : 2≤ownSlack p L before0) (pricedU0 : 2≤ownSlack p PreCage12.U before0)
 : Nonempty (Stage final outcomes) := by
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
 have prefixU : 2≤ownSlack p PreCage12.U globalBefore := by
   have nn := first.ownSlack_nonnegative Generated.soko1_2_potential_valid (endGroup PreCage12.U before0)
   change 0≤ownSlack p (endGroup PreCage12.U before0) before at nn
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
 have total:=NorthPriceBalance12.total logged completed
 have right:=NorthPriceBalance12.right_four logged completed
 change 4≤energy p Final222.R outcomes at right
 change energy p L outcomes+energy p Final222.R outcomes=Int.ofNat (1+pushes)-212 at total
 simp only[Int.ofNat_eq_natCast] at total
 have leftBudget:energy p L outcomes≤14:=by omega
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
       exact False.elim (CageFour12.blocked_impossible (List.Subset.trans globalLocks oldGroup.2)
         checked effect (block210 j middle.player hero adjacent))
     · have endingSame := push_effect_singleton soko1_2.initial.holes globalReached.holes_sublist.subset
         (show pushTargets soko1_2.board 238 .south=[264] by decide +kernel)
         (by decide +kernel) checked effect
       subst ending
       obtain ⟨result,adjacent,push⟩ := effect_push_data checked effect
       exact False.elim (CageFour12.blocked_impossible (List.Subset.trans globalLocks oldGroup.2)
         checked effect (block238 j middle.player hero adjacent))
     · have endingSame := push_effect_singleton soko1_2.initial.holes globalReached.holes_sublist.subset
         (show pushTargets soko1_2.board 265 .south=[291] by decide +kernel)
         (by decide +kernel) checked effect
       subst ending
       have tag:=NorthBudgetParity22912.current_tag firstGlobal j oldLocks fixedGlobal
       have lower:=North265Price23112.first265_lower_231 logged completed globalShape firstGlobal
         checked effect last j fixedGlobal tag
       omega
     · have endingSame := push_effect_singleton soko1_2.initial.holes globalReached.holes_sublist.subset
         (show pushTargets soko1_2.board 318 .west=[317] by decide +kernel)
         (by decide +kernel) checked effect
       subst ending
       have lower := North31823112.first318_lower231 logged completed globalShape firstGlobal
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
       have later := RingUpperElevenStrong12.energy_eleven
         last nextReached (update (endGroup L globalBefore) (.push 291 (.stay 290)))
         nextUnique nextSubset completed nextHero kept
       change 11≤energy p (update (endGroup L globalBefore) (.push 291 (.stay 290))) after at later
       have bound := reserve 2 11 (by decide +kernel) later
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
     let US:List Cell:=PreCage12.U++[213]
     have usUnique:US.Nodup:=by decide +kernel
     have usActual:US⊆FirstSplit12.afterN.boulders:=by decide +kernel
     have tags:=firstGlobal.end_split initialUnique PreCage12.U [213] usUnique usActual
     rw[uGlobal,sGlobal] at tags
     have pairBefore:([186,212]:List Cell)⊆endGroup US globalBefore:=by
       intro c member
       apply tags.mem_iff.mp
       have finite:([186,212]:List Cell)⊆UA++[212]:=by decide +kernel
       exact finite member
     have usFacts:=firstGlobal.end_subset initialUnique US usUnique usActual
     have usUniqueNext:=GhostSubset.update_unique middle t (.push 161 (.stay 135)) effect nextActual _ usFacts.1 usFacts.2
     have usSubsetNext:=GhostSubset.update_subset middle t (.push 161 (.stay 135)) effect _ usFacts.1 usFacts.2
     have pairAfter:=update_mono ([186,212]:List Cell) (endGroup US globalBefore) (by decide +kernel) pairBefore (.push 161 (.stay 135))
     simp only[update,move,if_neg (show (161:Cell)∉([186,212]:List Cell) by decide +kernel)] at pairAfter
     have pairHero:t.state.player∈VerticalPair12.region false 0:=by
       rw[matches_hero middle t (.push 161 (.stay 135)) effect];decide +kernel
     have later:=VerticalPair12.owned_energy_two false last nextReached _ usUniqueNext usSubsetNext pairHero pairAfter
     change 2≤energy p (update (endGroup US globalBefore) (.push 161 (.stay 135))) after at later
     have ownerU:(161:Cell)∈endGroup US globalBefore:=by
       apply tags.mem_iff.mp
       decide +kernel
     have prefixMono:=firstGlobal.ownSlack_mono Generated.soko1_2_potential_valid initialUnique
       PreCage12.U US (by decide +kernel) usUnique (by decide +kernel) usActual (by decide +kernel)
     change ownSlack p PreCage12.U globalBefore≤ownSlack p US globalBefore at prefixMono
     have usBound:12≤energy p US outcomes:=by
       rw[globalShape,energy_at_split]
       simp only[projectedOutcome,if_pos ownerU]
       have price:slack p (.push 161 (.stay 135))=8:=by decide +kernel
       rw[price]
       omega
     have gThree:3≤energy p NorthBound12.G outcomes:=by
       rcases NorthBound12.g_cases logged completed with four|⟨three,_⟩
       ·change 4≤energy p NorthBound12.G outcomes at four;omega
       ·exact three
     have add:=TwoReserves12.add_le_energy logged Generated.soko1_2_potential_valid initialUnique
       US NorthBound12.G L (by decide +kernel) lUnique lSubset (by decide +kernel)
     change energy p US outcomes+energy p NorthBound12.G outcomes≤energy p L outcomes at add
     have lower:15≤energy p L outcomes:=by omega
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
     exact ⟨{
       state:=t.state,beforeDirs:=_,beforePushes:=_,beforeMoves:=_,before:=before1,
       afterDirs:=_,afterPushes:=_,afterMoves:=_,after:=after,
       shape:=shape1,first:=lead1,last:=last,phase:=j,hero:=nextHero,
       inside:=gsAfter,sAt:=sAfter,fixed:=fixedAfter,paid:=pricedSAfter }⟩
#print axioms to_s211
end Owner1007.North187ToS23012
