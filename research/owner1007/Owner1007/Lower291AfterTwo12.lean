import Owner1007.Lower291Trade12
import Owner1007.NorthTight22812
namespace Owner1007.Lower291AfterTwo12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
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
 (owner : (265:Cell)∈endGroup NorthBound12.J before)
 (j : Fin 5)
 (bottomTag : (endGroup NorthBound12.BottomN before).Perm [318,NorthEvents12.current j]) :False := by
 have actualUnique : FirstSplit12.afterN.boulders.Nodup := by decide +kernel
 have atReached := NorthBound12.north_reached.append first.trace
 have atUnique := atReached.boulders_nodup (by decide +kernel)
 have nextReached := atReached.append (Trace.cons head (Trace.nil t.state))
 have nextActual := step_boulders_nodup _ _ _ _ atUnique head
 have jFacts := first.end_subset actualUnique NorthBound12.J (by decide +kernel) (by decide +kernel)
 have nextJUnique := GhostSubset.update_unique middle t (.push 265 (.stay 291)) effect nextActual
   (endGroup NorthBound12.J before) jFacts.1 jFacts.2
 have nextJSubset := GhostSubset.update_subset middle t (.push 265 (.stay 291)) effect
   (endGroup NorthBound12.J before) jFacts.1 jFacts.2
 have bFacts := first.end_subset actualUnique NorthBound12.BottomN (by decide +kernel) (by decide +kernel)
 have bPhysical : ([318,NorthEvents12.current j]:List Cell)⊆middle.boulders :=
   List.Subset.trans bottomTag.symm.subset bFacts.2
 obtain ⟨result,_,pushed⟩ := effect_push_data head effect
 obtain ⟨dest,next,_,_,clear⟩ := (push_first_clear soko1_2.board middle 265 .south result pushed).2
 have destEq : dest=291 := Option.some.inj (next.symm.trans (by decide +kernel : advance soko1_2.board 265 .south=some 291))
 subst dest
 have away : NorthEvents12.current j≠291 := by
   intro same
   have present : (291:Cell)∈middle.boulders := bPhysical (by rw [same];simp)
   exact clear present
 have small : j.val<4 := by
   have check : ∀ j,NorthEvents12.current j≠291→j.val<4 := by decide +kernel
   exact check j away
 let i : Fin 4 := ⟨j.val,small⟩
 have currentEq : After26512.current i=NorthEvents12.current j := by
   have check : ∀ (i:Fin 4) (j:Fin 5),i.val=j.val→After26512.current i=NorthEvents12.current j := by decide +kernel
   exact check i j rfl
 have bUnique : ([318,NorthEvents12.current j]:List Cell).Nodup := bottomTag.nodup_iff.mp bFacts.1
 have no265 : (265:Cell)∉([318,NorthEvents12.current j]:List Cell) := by
   have check : ∀ j,(265:Cell)∉([318,NorthEvents12.current j]:List Cell) := by decide +kernel
   exact check j
 have bKept := GhostSubset.update_subset middle t (.push 265 (.stay 291)) effect
   [318,NorthEvents12.current j] bUnique bPhysical
 have bUpdate : update [318,NorthEvents12.current j] (.push 265 (.stay 291))=[318,NorthEvents12.current j] := by
   simp only [update,move,if_neg no265]
 rw [bUpdate] at bKept
 have present291 : (291:Cell)∈t.state.boulders := by
   rw [effect.2]
   exact List.mem_cons_self
 have inside : After26512.locks i⊆t.state.boulders := by
   change ([291,318,After26512.current i]:List Cell)⊆t.state.boulders
   rw [currentEq]
   intro c member
   rcases List.mem_cons.mp member with same|bottom
   ·simpa only [same] using present291
   ·exact bKept bottom
 have hero : t.state.player∈After26512.region i := by
   rw [matches_hero middle t (.push 265 (.stay 291)) effect]
   exact After26512.start_hero i
 have trade := Lower291Trade12.trade last nextReached completed i hero inside
 change 2≤energy p [291] after∨3≤energy p [318,After26512.current i] after at trade
 rw [currentEq] at trade
 have eight := (NorthTight22812.canonical_ledgers logged completed cheap).2.2.1
 change energy p NorthBound12.G outcomes=8 at eight
 have bottom := NorthBound12.bottom_north_energy_two logged
 change 2≤energy p NorthBound12.BottomN outcomes at bottom
 have split := logged.energy_split actualUnique p NorthBound12.J NorthBound12.BottomN
   (by decide +kernel) (by decide +kernel)
 change energy p NorthBound12.G outcomes=energy p NorthBound12.J outcomes+energy p NorthBound12.BottomN outcomes at split
 have one : slack p (.push 265 (.stay 291))=2 := by decide +kernel
 have jLedger : energy p NorthBound12.J outcomes=ownSlack p NorthBound12.J before+2+
     energy p (update (endGroup NorthBound12.J before) (.push 265 (.stay 291))) after := by
   rw [shape,energy_at_split]
   simp only [projectedOutcome,if_pos owner,one]
 have nextJNN := last.energy_nonnegative Generated.soko1_2_potential_valid
   (update (endGroup NorthBound12.J before) (.push 265 (.stay 291)))
 change 0≤energy p (update (endGroup NorthBound12.J before) (.push 265 (.stay 291))) after at nextJNN
 have noBottom265 : (265:Cell)∉endGroup NorthBound12.BottomN before :=
   fun h=>no265 (bottomTag.subset h)
 have bLedger : energy p NorthBound12.BottomN outcomes=ownSlack p NorthBound12.BottomN before+
     energy p (endGroup NorthBound12.BottomN before) after := by
   rw [shape,energy_at_split]
   simp only [projectedOutcome,if_neg noBottom265,slack,update,move,if_neg noBottom265,Int.add_zero]
 have bPrefixNN := first.ownSlack_nonnegative Generated.soko1_2_potential_valid NorthBound12.BottomN
 change 0≤ownSlack p NorthBound12.BottomN before at bPrefixNN
 have sameBottom := energy_perm p bottomTag after
 rcases trade with nextCore|nextBottom
 · have singleInside : ([291]:List Cell)⊆update (endGroup NorthBound12.J before) (.push 265 (.stay 291)) := by
     simp only [update,move,if_pos owner,post]
     intro c found
     have same : c=291 := List.mem_singleton.mp found
     subst c
     exact List.mem_cons_self
   have mono := last.energy_mono Generated.soko1_2_potential_valid nextActual [291]
     (update (endGroup NorthBound12.J before) (.push 265 (.stay 291))) (by decide +kernel)
     nextJUnique (List.Subset.trans singleInside nextJSubset) nextJSubset singleInside
   change energy p [291] after≤energy p (update (endGroup NorthBound12.J before) (.push 265 (.stay 291))) after at mono
   omega
 · omega
#print axioms impossible
end Owner1007.Lower291AfterTwo12
