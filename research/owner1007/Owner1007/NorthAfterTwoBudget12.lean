import Owner1007.AfterTwoOrdinaryTrap12
import Owner1007.After210236Five12
import Owner1007.After238210Five12
import Owner1007.NorthTight22812
import Owner1007.Lower291OwnedActivation12
namespace Owner1007.NorthAfterTwoBudget12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12 Owner1007.AfterTwoOrdinaryTrap12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem impossible
 {final dirs pushes moves outcomes state beforeDirs beforePushes beforeMoves before afterDirs afterPushes afterMoves after}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : 1+pushes≤228)
 (shape : outcomes=before++after)
 (first : Logged soko1_2.board FirstSplit12.afterN beforeDirs state beforePushes beforeMoves before)
 (last : Logged soko1_2.board state afterDirs final afterPushes afterMoves after)
 (paid : 4≤ownSlack p NorthBound12.J before)
 (kind : Fin 2) (i : Fin 5)
 (coreTag : (endGroup NorthBound12.J before).Perm (C kind))
 (hero : state.player∈R kind i) (inside : K kind i⊆endGroup NorthBound12.G before) :False := by
 have initialUnique : FirstSplit12.afterN.boulders.Nodup := by decide +kernel
 have reached := NorthBound12.north_reached.append first.trace
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 have groupFacts := first.end_subset initialUnique NorthBound12.G (by decide +kernel) (by decide +kernel)
 have physical := List.Subset.trans inside groupFacts.2
 have splitBefore := first.end_split initialUnique NorthBound12.J NorthBound12.BottomN
   (by decide +kernel) (by decide +kernel)
 change (endGroup NorthBound12.J before++endGroup NorthBound12.BottomN before).Perm
   (endGroup NorthBound12.G before) at splitBefore
 have lowerInside : ∀ kind i,B i⊆K kind i := by decide +kernel
 have away : ∀ kind i,∀ c∈B i,c∉C kind := by decide +kernel
 have bottomSubset : B i⊆endGroup NorthBound12.BottomN before := by
   intro c member
   have both := splitBefore.mem_iff.mpr (inside (lowerInside kind i member))
   rcases List.mem_append.mp both with core|bottom
   ·exact False.elim (away kind i c member (coreTag.subset core))
   ·exact bottom
 have bUnique : (B i).Nodup := by
   have check : ∀ i,(B i).Nodup := by decide +kernel
   exact check i
 have bFacts := first.end_subset initialUnique NorthBound12.BottomN (by decide +kernel) (by decide +kernel)
 have short := endGroup_length_le NorthBound12.BottomN before
 change (endGroup NorthBound12.BottomN before).length≤2 at short
 have bLength : (B i).length=2 := by rfl
 have bottomTag := Lower291OwnedActivation12.perm_of_subset_short bUnique bFacts.1 bottomSubset
   (by rw [bLength];exact short)
 have eight := (NorthTight22812.canonical_ledgers logged completed cheap).2.2.1
 change energy p NorthBound12.G outcomes=8 at eight
 have bottom := NorthBound12.bottom_north_energy_two logged
 change 2≤energy p NorthBound12.BottomN outcomes at bottom
 have globalSplit := logged.energy_split initialUnique p NorthBound12.J NorthBound12.BottomN
   (by decide +kernel) (by decide +kernel)
 change energy p NorthBound12.G outcomes=energy p NorthBound12.J outcomes+energy p NorthBound12.BottomN outcomes at globalSplit
 have coreLedger := TokenAccounting.energy_append p NorthBound12.J before after
 rw [←shape] at coreLedger
 have coreEnergyEq := energy_perm p coreTag after
 have coreCheap : energy p (C kind) after≤2 := by omega
 have prefixMono := first.ownSlack_mono Generated.soko1_2_potential_valid initialUnique
   NorthBound12.J NorthBound12.G (by decide +kernel) (by decide +kernel)
   (by decide +kernel) (by decide +kernel) (by decide +kernel)
 change ownSlack p NorthBound12.J before≤ownSlack p NorthBound12.G before at prefixMono
 have groupLedger := TokenAccounting.energy_append p NorthBound12.G before after
 rw [←shape] at groupLedger
 have groupCheap : energy p (endGroup NorthBound12.G before) after≤4 := by omega
 have coreTwo : 2≤energy p (C kind) after := by
   obtain ⟨k,h⟩ := kind
   have cases : k=0∨k=1 := by omega
   rcases cases with rfl|rfl
   ·have found := After210236Five12.cash_cases_five last reached completed
      (endGroup NorthBound12.G before) groupFacts.1 groupFacts.2 i hero inside
    rcases found with core|large
    ·exact core
    ·change 5≤energy p (endGroup NorthBound12.G before) after at large
     omega
   ·have found := After238210Five12.cash_cases_five last reached completed
      (endGroup NorthBound12.G before) groupFacts.1 groupFacts.2 i hero inside
    rcases found with core|large
    ·exact core
    ·change 5≤energy p (endGroup NorthBound12.G before) after at large
     omega
 have pairUnique := splitBefore.nodup_iff.mpr groupFacts.1
 have pairActual := List.Subset.trans splitBefore.subset groupFacts.2
 have localSplit := last.energy_split actualUnique p
   (endGroup NorthBound12.J before) (endGroup NorthBound12.BottomN before) pairUnique pairActual
 have localPerm := energy_perm p splitBefore after
 have bottomEnergyEq := energy_perm p bottomTag after
 have bottomCheap : energy p (B i) after≤2 := by omega
 exact AfterTwoOrdinaryTrap12.impossible last reached completed kind i hero physical coreCheap bottomCheap
#print axioms impossible
end Owner1007.NorthAfterTwoBudget12
