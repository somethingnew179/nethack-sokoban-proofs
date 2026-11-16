import Owner1007.After238210Bound12
import Owner1007.LowerBCut12
import Owner1007.After265ZeroCore12
import Owner1007.Lower291OwnedActivation12
namespace Owner1007.AfterTwoMixedTrap12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12 Owner1007.After23821012
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def B (i : Fin 5) : List Cell := [318,NorthEvents12.current i]
theorem joint_perm : ∀ i,(ordinary++B i).Perm (locks i) := by decide +kernel
theorem bottom_inside : ∀ i,B i⊆locks i := by decide +kernel
theorem bottom_away : ∀ i,∀ c∈B i,c∉ordinary := by decide +kernel

theorem impossible {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (completed : Goal final) (i : Fin 5)
 (hero0 : state.player∈region i) (inside : locks i⊆state.boulders)
 (coreCheap : energy p ordinary outcomes≤2) (bottomCheap : energy p (B i) outcomes≤2) :False := by
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 have closed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ matrix
 have jointUnique : (ordinary++B i).Nodup := (joint_perm i).nodup_iff.mpr (unique i)
 have jointActual := List.Subset.trans (joint_perm i).subset inside
 have coreActual : ordinary⊆state.boulders :=
   List.Subset.trans (List.subset_append_left ordinary (B i)) jointActual
 have bActual : B i⊆state.boulders := List.Subset.trans (bottom_inside i) inside
 have coreUnique : ordinary.Nodup := by decide +kernel
 have bUnique : (B i).Nodup := by
   have check : ∀ i,(B i).Nodup := by decide +kernel
   exact check i
 have exactSplit := logged.energy_split actualUnique p ordinary (B i) jointUnique jointActual
 have exactPerm := energy_perm p (joint_perm i) outcomes
 have jointCheap : energy p (locks i) outcomes≤4 := by omega
 rcases event_or_good closed unique logged reached (locks i) (unique i) inside hero0 (fun _ h=>h) with event|terminal
 · obtain ⟨bd,bp,bm,before,middle,dir,t,outcome,after,ad,ap,am,j,shape,first,checked,effect,last,heroOne,locksOne,pays,fixedBefore⟩ :=
     event.split_fixed fixed fixed_inside fixed_guard reached (unique i) inside
   have atReached := reached.append first.trace
   have atUnique := atReached.boulders_nodup (by decide +kernel)
   have old := first.end_subset actualUnique (locks i) (unique i) inside
   have priorCore := fixedBefore ordinary (fun c h=>List.mem_append_left _ h)
   have pairSplit := first.end_split actualUnique ordinary (B i) jointUnique jointActual
   have transport := endGroup_perm (joint_perm i) before
   have together := pairSplit.trans transport
   rw [priorCore] at together
   have bFacts := first.end_subset actualUnique (B i) bUnique bActual
   have bottomSubset : B j⊆endGroup (B i) before := by
     intro c member
     have both := together.mem_iff.mpr (locksOne (bottom_inside j member))
     rcases List.mem_append.mp both with core|bottom
     ·exact False.elim (bottom_away j c member core)
     ·exact bottom
   have newBUnique : (B j).Nodup := by
     have check : ∀ j,(B j).Nodup := by decide +kernel
     exact check j
   have short := endGroup_length_le (B i) before
   have length : (endGroup (B i) before).length≤(B j).length := by
     have all : ∀ j,(B j).length=2 := by decide +kernel
     rw [all i] at short
     rw [all j]
     exact short
   have bottomTag := Lower291OwnedActivation12.perm_of_subset_short newBUnique bFacts.1 bottomSubset length
   have bottomPhysical := List.Subset.trans bottomTag.symm.subset bFacts.2
   cases outcome with
   | walk target=>exact False.elim pays
   | push source ending=>
     obtain ⟨owner,headPaid⟩:=pays
     have rawPrice := push_effect_price p soko1_2.initial.holes (if source=318 then (3:Int) else 2)
       atReached.holes_sublist.subset (priced_min headPaid) checked effect
     have nextActual := step_boulders_nodup _ _ _ _ atUnique checked
     have nextReached := atReached.append (Trace.cons checked (Trace.nil t.state))
     rcases headPaid with ⟨choices,south⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
     · subst dir
       have member : source∈ordinary := by
         rcases choices with rfl|rfl|rfl <;>decide +kernel
       have not318 : source≠318 := by
         have check : ∀ c∈ordinary,c≠318 := by decide +kernel
         exact check source member
       rw [if_neg not318] at rawPrice
       have coreFacts := first.end_subset actualUnique ordinary coreUnique coreActual
       rw [priorCore] at coreFacts
       have nextCoreUnique := GhostSubset.update_unique middle t (.push source ending) effect nextActual ordinary coreUnique coreFacts.2
       have nextCoreSubset := GhostSubset.update_subset middle t (.push source ending) effect ordinary coreUnique coreFacts.2
       have prefixCoreNN := first.ownSlack_nonnegative Generated.soko1_2_potential_valid ordinary
       have nextCoreNN := last.energy_nonnegative Generated.soko1_2_potential_valid (update ordinary (.push source ending))
       change 0≤ownSlack p ordinary before at prefixCoreNN
       change 0≤energy p (update ordinary (.push source ending)) after at nextCoreNN
       have coreLedger : energy p ordinary outcomes=ownSlack p ordinary before+slack p (.push source ending)+
           energy p (update ordinary (.push source ending)) after := by
         rw [shape,energy_at_split,priorCore]
         simp only [projectedOutcome,if_pos member]
       have tailCoreZero : energy p (update ordinary (.push source ending)) after≤0 := by omega
       have notBj : source∉B j := by
         intro h
         exact bottom_away j source h member
       have notOldBottom : source∉endGroup (B i) before := fun h=>notBj (bottomTag.subset h)
       have prefixBottomNN := first.ownSlack_nonnegative Generated.soko1_2_potential_valid (B i)
       change 0≤ownSlack p (B i) before at prefixBottomNN
       have bottomLedger : energy p (B i) outcomes=ownSlack p (B i) before+energy p (endGroup (B i) before) after := by
         rw [shape,energy_at_split]
         simp only [projectedOutcome,if_neg notOldBottom,slack,update,move,if_neg notOldBottom,Int.add_zero]
       have bottomEnergyEq := energy_perm p bottomTag after
       have tailBottomCheap : energy p (B j) after≤2 := by omega
       have nextBottom := GhostSubset.update_subset middle t (.push source ending) effect (B j) newBUnique bottomPhysical
       have bottomUpdate : update (B j) (.push source ending)=B j := by simp only [update,move,if_neg notBj]
       rw [bottomUpdate] at nextBottom
       rcases choices with rfl|rfl|rfl
       · have sameEnding := push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset
           (show pushTargets soko1_2.board 236 .south=[262] by decide +kernel) (by decide +kernel) checked effect
         subst ending
         have lowerInside : LowerBCut12.C⊆update ordinary (.push 236 (.stay 262)) := by decide +kernel
         have physicalLower : LowerBCut12.locks j⊆t.state.boulders :=
           List.append_subset.mpr ⟨List.Subset.trans lowerInside nextCoreSubset,nextBottom⟩
         have nextHero : t.state.player∈LowerBCut12.region j := by
           rw [matches_hero middle t (.push 236 (.stay 262)) effect]
           exact LowerBCut12.hero j 236 (by decide +kernel)
         have mono := last.energy_mono Generated.soko1_2_potential_valid nextActual LowerBCut12.C
           (update ordinary (.push 236 (.stay 262))) (by decide +kernel) nextCoreUnique
           (List.Subset.trans lowerInside nextCoreSubset) nextCoreSubset lowerInside
         change energy p LowerBCut12.C after≤energy p (update ordinary (.push 236 (.stay 262))) after at mono
         have coreZero : energy p LowerBCut12.C after≤0 := by omega
         exact LowerBCut12.impossible last nextReached completed j nextHero physicalLower coreZero tailBottomCheap
       · have highPrice := push_effect_price p soko1_2.initial.holes 4 atReached.holes_sublist.subset
           (show ∀ dest∈pushTargets soko1_2.board 264 .south,
             dest∉soko1_2.initial.holes∧(4:Int)≤1+p.boulder dest-p.boulder 264 from by decide +kernel) checked effect
         omega
       · have sameEnding := push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset
           (show pushTargets soko1_2.board 265 .south=[291] by decide +kernel) (by decide +kernel) checked effect
         subst ending
         have owner291 : (291:Cell)∈update ordinary (.push 265 (.stay 291)) := by decide +kernel
         exact After265ZeroCore12.impossible checked effect last atReached completed
           (update ordinary (.push 265 (.stay 291))) nextCoreUnique nextCoreSubset owner291 j
           bottomPhysical tailCoreZero tailBottomCheap
     · have mono := first.end_mono actualUnique [318] (B i) (by decide +kernel)
         (List.Subset.trans ((show ∀ k,([318]:List Cell)⊆locks k from by decide +kernel) i) inside)
         (by simp [B])
       have prior := fixedBefore [318] (by decide +kernel)
       have ownBottom : (318:Cell)∈endGroup (B i) before := by
         apply mono
         rw [prior]
         simp
       have bound := event_energy_le Generated.soko1_2_potential_valid (B i) first last (.push 318 ending)
       simp only [projectedOutcome,if_pos ownBottom] at bound
       rw [←shape] at bound
       change slack p (.push 318 ending)≤energy p (B i) outcomes at bound
       have three : (3:Int)≤slack p (.push 318 ending) := by simpa using rawPrice
       omega
     · have sameEnding := push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset
         NorthEvents12.ring_activation (by decide +kernel) checked effect
       subst ending
       have shift : ∀ j,Residual29012.locks 0⊆290::(locks j).erase 291 := by decide +kernel
       have kept := CageFour12.shifted_inside (unique j) locksOne owner (shift j)
       have nextUnique := GhostSubset.update_unique middle t (.push 291 (.stay 290)) effect nextActual
         (endGroup (locks i) before) old.1 old.2
       have nextSubset := GhostSubset.update_subset middle t (.push 291 (.stay 290)) effect
         (endGroup (locks i) before) old.1 old.2
       have nextHero : t.state.player∈Residual29012.region 0 := by
         rw [matches_hero middle t (.push 291 (.stay 290)) effect]
         decide +kernel
       have later := Residual290Any12.owned_energy_credit Residual29012.matrix last nextReached
         (update (endGroup (locks i) before) (.push 291 (.stay 290))) nextUnique nextSubset 0 nextHero kept
       change 5≤energy p (update (endGroup (locks i) before) (.push 291 (.stay 290))) after at later
       have prefixNN := first.ownSlack_nonnegative Generated.soko1_2_potential_valid (locks i)
       change 0≤ownSlack p (locks i) before at prefixNN
       have one : slack p (.push 291 (.stay 290))=2 := by decide +kernel
       have whole := energy_at_split p (locks i) before (.push 291 (.stay 290)) after
       rw [←shape] at whole
       simp only [projectedOutcome,if_pos owner,one] at whole
       omega
 · obtain ⟨j,_,kept⟩:=terminal
   have endInside := logged.end_subset actualUnique (locks i) (unique i) inside
   have count := List.Nodup.length_le_of_subset (unique j) (List.Subset.trans kept endInside.2)
   rw [size j] at count
   have conserved := (reached.append logged.trace).conservation
   have empty : final.holes=[] := completed
   change 20+final.holes.length=final.boulders.length+18 at conserved
   rw [empty] at conserved
   simp only [List.length_nil] at conserved
   omega
#print axioms impossible
end Owner1007.AfterTwoMixedTrap12
