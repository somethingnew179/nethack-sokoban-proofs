import Owner1007.SidecarCriticalFixed12
namespace Owner1007.North238CashNo26412
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
open Owner1007.SidecarCoreQuiet12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem cash_split
 {final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : 1+pushes≤228)
 {d0 p0 m0 before middle t after d1 p1 m1}
 (shape : outcomes=before++.push 238 (.stay 264)::after)
 (first : Logged soko1_2.board FirstSplit12.afterN d0 middle p0 m0 before)
 (head : step soko1_2.board middle .south=some t)
 (effect : Matches middle t (.push 238 (.stay 264)))
 (last : Logged soko1_2.board t.state d1 final p1 m1 after)
 (j : Fin 5) (oldLocks : NorthEvents12.locks j⊆endGroup NorthBound12.G before)
 (fixedGlobal : ∀ small : List Cell,small⊆NorthEvents12.J→endGroup small before=small)
 (sGlobal : endGroup [213] before=[211]) :
 ∃ bd bp bm between mid dir actor source ending rest ad ap am,∃ i : Fin 5,
 after=between++.push source ending::rest ∧
 Logged soko1_2.board t.state bd mid bp bm between ∧
 step soko1_2.board mid dir=some actor ∧Matches mid actor (.push source ending) ∧
 Logged soko1_2.board actor.state ad final ap am rest ∧
 mid.player∈AfterJ12.region 1 i ∧
 AfterJ12.locks 1 i⊆endGroup (update (endGroup NorthBound12.G before) (.push 238 (.stay 264))) between ∧
 source∈endGroup (update (endGroup NorthBound12.G before) (.push 238 (.stay 264))) between ∧
 AfterJ12.paid 1 source dir ∧
 (∀ small : List Cell,small⊆AfterJ12.fixed 1→endGroup small between=small) ∧source≠264 := by
 have initialUnique : FirstSplit12.afterN.boulders.Nodup := by decide +kernel
 have reached := NorthBound12.north_reached.append first.trace
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 have facts := first.end_subset initialUnique NorthBound12.G (by decide +kernel) (by decide +kernel)
 have nextActual := step_boulders_nodup _ _ _ _ actualUnique head
 have nextUnique := GhostSubset.update_unique middle t (.push 238 (.stay 264)) effect nextActual
   (endGroup NorthBound12.G before) facts.1 facts.2
 have nextSubset := GhostSubset.update_subset middle t (.push 238 (.stay 264)) effect
   (endGroup NorthBound12.G before) facts.1 facts.2
 have nextReached := reached.append (Trace.cons head (Trace.nil t.state))
 have owner : (238:Cell)∈endGroup NorthBound12.G before := by
   have check : ∀ j,(238:Cell)∈NorthEvents12.locks j := by decide +kernel
   exact oldLocks (check j)
 have activation : ∀ j,AfterJ12.locks 1 j⊆264::(NorthEvents12.locks j).erase 238 := by decide +kernel
 have nextLocks := CageFour12.shifted_inside (NorthEvents12.unique j) oldLocks owner (activation j)
 have nextHero : t.state.player∈AfterJ12.region 1 j := by
   rw [matches_hero middle t (.push 238 (.stay 264)) effect]
   have check : ∀ j,(238:Cell)∈AfterJ12.region 1 j := by decide +kernel
   exact check j
 have closed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ (AfterJ12.matrix 1)
 have found : EventLog (AfterJ12.locks 1) (AfterJ12.region 1) (AfterJ12.paid 1)
     (update (endGroup NorthBound12.G before) (.push 238 (.stay 264))) t.state d1 final p1 m1 after := by
   rcases event_or_good closed (AfterJ12.unique 1) last nextReached _ nextUnique nextSubset nextHero nextLocks with event|terminal
   · exact event
   · obtain ⟨k,_,kept⟩ := terminal
     have endInside := last.end_subset nextActual _ nextUnique nextSubset
     have count := List.Nodup.length_le_of_subset (AfterJ12.unique 1 k) (List.Subset.trans kept endInside.2)
     rw [AfterJ12.size 1 k] at count
     have conserved := (nextReached.append last.trace).conservation
     have empty : final.holes=[] := completed
     change 20+final.holes.length=final.boulders.length+18 at conserved
     rw [empty] at conserved
     simp only [List.length_nil] at conserved
     omega
 obtain ⟨bd,bp,bm,between,mid,dir,actor,outcome,rest,ad,ap,am,i,shape2,lead,checked,matched,tail,hero,locks,pays,unchanged⟩ :=
   found.split_fixed (AfterJ12.fixed 1) (AfterJ12.fixed_inside 1) (AfterJ12.fixed_guard 1)
     nextReached nextUnique nextSubset
 cases outcome with
 | walk target => exact False.elim pays
 | push source ending =>
   obtain ⟨own,paid⟩ := pays
   have not264 : source≠264 := by
     intro same
     subst source
     have onlySouth : ∀ dir∈allDirs,AfterJ12.paid 1 264 dir→dir=.south := by decide +kernel
     have direction := onlySouth dir (Geometry.all_directions dir) paid
     subst dir
     have atReached := nextReached.append lead.trace
     have sameEnding := push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset
       (show pushTargets soko1_2.board 264 .south=[290] by decide +kernel) (by decide +kernel) checked matched
     subst ending
     have fullShape : outcomes=before++.push 238 (.stay 264)::(between++.push 264 (.stay 290)::rest) := by
       rw [shape,shape2]
     have wholeLocks : AfterJ12.locks 1 i⊆endGroup NorthBound12.G (before++.push 238 (.stay 264)::between) := by
       simpa only [endGroup_append,endGroup] using locks
     exact SidecarCriticalFixed12.impossible logged completed cheap fullShape first head effect
       lead checked matched tail
       (fixedGlobal (Core 0) (by decide +kernel))
       (unchanged (Core 1) (by decide +kernel))
       sGlobal i wholeLocks
   exact ⟨bd,bp,bm,between,mid,dir,actor,source,ending,rest,ad,ap,am,i,shape2,lead,
     checked,matched,tail,hero,locks,own,paid,unchanged,not264⟩
#print axioms cash_split
end Owner1007.North238CashNo26412
