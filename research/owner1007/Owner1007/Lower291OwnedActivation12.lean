import Owner1007.Lower291AfterTwo12
import Owner1007.After21023612
import Owner1007.After23821012
namespace Owner1007.Lower291OwnedActivation12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
theorem perm_of_subset_short {small large : List Cell}
 (smallUnique : small.Nodup) (largeUnique : large.Nodup) (subset : small⊆large)
 (length : large.length≤small.length) : large.Perm small := by
 have reverse : large⊆small := by
   intro c member
   apply Classical.byContradiction
   intro outside
   have newUnique : (c::small).Nodup := List.nodup_cons.mpr ⟨outside,smallUnique⟩
   have all : c::small⊆large := List.cons_subset.mpr ⟨member,subset⟩
   have long := List.Nodup.length_le_of_subset newUnique all
   simp only [List.length_cons] at long
   omega
 exact (List.perm_ext_iff_of_nodup largeUnique smallUnique).mpr
   (fun c=>⟨fun h=>reverse h,fun h=>subset h⟩)

def ordinary (kind : Fin 2) : List Cell :=
 if kind.val=0 then After21023612.ordinary else After23821012.ordinary
def locks (kind : Fin 2) (j : Fin 5) : List Cell :=
 if kind.val=0 then After21023612.locks j else After23821012.locks j
theorem lower_inside : ∀ kind j,([318,NorthEvents12.current j]:List Cell)⊆locks kind j := by decide +kernel
theorem away : ∀ kind j,∀ c∈([318,NorthEvents12.current j]:List Cell),c∉ordinary kind := by decide +kernel
theorem owner : ∀ kind,(265:Cell)∈ordinary kind := by decide +kernel

theorem impossible
 {final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : 1+pushes≤228)
 {bd bp bm before middle t after ad ap am}
 (shape : outcomes=before++.push 265 (.stay 291)::after)
 (first : Logged soko1_2.board FirstSplit12.afterN bd middle bp bm before)
 (head : step soko1_2.board middle .south=some t)
 (effect : Matches middle t (.push 265 (.stay 291)))
 (last : Logged soko1_2.board t.state ad final ap am after)
 (priorPaid : 4≤ownSlack p NorthBound12.J before)
 (kind : Fin 2) (j : Fin 5)
 (coreTag : (endGroup NorthBound12.J before).Perm (ordinary kind))
 (inside : locks kind j⊆endGroup NorthBound12.G before) :False := by
 have actualUnique : FirstSplit12.afterN.boulders.Nodup := by decide +kernel
 have split := first.end_split actualUnique NorthBound12.J NorthBound12.BottomN
   (by decide +kernel) (by decide +kernel)
 change (endGroup NorthBound12.J before++endGroup NorthBound12.BottomN before).Perm
   (endGroup NorthBound12.G before) at split
 have bottomSubset : ([318,NorthEvents12.current j]:List Cell)⊆endGroup NorthBound12.BottomN before := by
   intro c member
   have large := inside (lower_inside kind j member)
   have both := split.mem_iff.mpr large
   rcases List.mem_append.mp both with core|bottom
   · exact False.elim (away kind j c member (coreTag.subset core))
   · exact bottom
 have smallUnique : ([318,NorthEvents12.current j]:List Cell).Nodup := by
   have check : ∀ j,([318,NorthEvents12.current j]:List Cell).Nodup := by decide +kernel
   exact check j
 have facts := first.end_subset actualUnique NorthBound12.BottomN (by decide +kernel) (by decide +kernel)
 have length := endGroup_length_le NorthBound12.BottomN before
 change (endGroup NorthBound12.BottomN before).length≤2 at length
 have bottomTag := perm_of_subset_short smallUnique facts.1 bottomSubset length
 have own265 : (265:Cell)∈endGroup NorthBound12.J before := coreTag.symm.subset (owner kind)
 exact Lower291AfterTwo12.impossible logged completed cheap shape first head effect last
   priorPaid own265 j bottomTag
#print axioms impossible
end Owner1007.Lower291OwnedActivation12
