import Owner1007.Inward191Eight11
namespace Owner1007.CorralQuietCell11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- A foreign/current cell need not be an original stationary identity:
inaccessibility of every initiating player position keeps it untouched. -/
theorem cell_zero {n : Nat} {locks region : Fin n→List Cell} {paid : Cell→Dir→Prop}
 (closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid)
 (uniqueLocks : ∀i,(locks i).Nodup) (cell : Cell)
 (away : ∀i,∀hero∈region i,∀dir,advance soko1_1.board hero dir=some cell→False)
 {state group dirs final pushes moves outcomes}
 (quiet : UpperQuiet11.Quiet paid state group dirs final pushes moves outcomes)
 (actual : state.boulders.Nodup) (unique : group.Nodup) (inside : group⊆state.boulders)
 (good : OwnedCorral11.Good locks region state group)
 (holes : state.holes⊆soko1_1.initial.holes) : ownPushes [cell] outcomes=0 := by
 induction quiet with
 | nil => rfl
 | @cons state group dir t rest final pushes moves outcome outcomes head effect avoid tail ih =>
   have firstZero : ownPush [cell] outcome=0 := by
     cases outcome with
     | walk target => rfl
     | push source ending =>
       by_cases same : source=cell
       · subst source
         have metadata : t.pushSource=some cell := by
           cases ending with
           | stay landing => rw [effect.2]
           | fill hole => rw [effect.2.2]
         obtain ⟨i,hero,_⟩ := good
         exact False.elim (away i state.player hero dir (PairPost11.source_adjacent head metadata))
       · have absent : source∉[cell] := by simpa only [List.mem_singleton] using same
         simp only [ownPush,if_neg absent]
   have unchanged := ownPush_zero_update [cell] outcome firstZero
   have nextActual := step_boulders_nodup _ _ _ _ actual head
   have nextUnique := GhostSubset.update_unique _ _ _ effect nextActual _ unique inside
   have nextInside := GhostSubset.update_subset _ _ _ effect _ unique inside
   have nextGood := OwnedCorralAny11.step_good_except closed uniqueLocks good inside holes head effect avoid
   have nextHoles := List.Subset.trans (step_holes_sublist _ _ _ _ head).subset holes
   have later := ih nextActual nextUnique nextInside nextGood nextHoles
   simpa only [ownPushes,firstZero,unchanged,Nat.zero_add] using later

theorem inward193_away : ∀i,∀hero∈Inward191Eight11.region i,∀dir∈allDirs,
 advance soko1_1.board hero dir=some 193→False := by decide +kernel

theorem inward193_zero {state group dirs final pushes moves outcomes}
 (quiet : UpperQuiet11.Quiet Inward191Eight11.paid state group dirs final pushes moves outcomes)
 (actual : state.boulders.Nodup) (unique : group.Nodup) (inside : group⊆state.boulders)
 (good : OwnedCorral11.Good Inward191Eight11.locks Inward191Eight11.region state group)
 (holes : state.holes⊆soko1_1.initial.holes) : ownPushes [193] outcomes=0 := by
 exact cell_zero Inward191Eight11.closed Inward191Eight11.unique 193
   (by intro i hero found dir adjacent;exact inward193_away i hero found dir (Geometry.all_directions dir) adjacent)
   quiet actual unique inside good holes
#print axioms cell_zero
#print axioms inward193_away
#print axioms inward193_zero
end Owner1007.CorralQuietCell11
