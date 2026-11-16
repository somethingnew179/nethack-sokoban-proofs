import Owner1007.Spare315Word32711
import Owner1007.TightRowPairs11
namespace Owner1007.TightRowPairs32711
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem other_capacity {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤327)
 (group : List Cell) (unique : group.Nodup) (inside : group⊆final.boulders)
 (away : ∀c,c∈group→c∉([314,315,316,317] : List Cell)) : group.length≤1 := by
 obtain ⟨cell,member,tag⟩ := Spare315Word32711.final_tag logged completed cheap
 have selected := (logged.end_subset (by decide) [315] (by decide) (by decide)).2
 have present : cell∈final.boulders := selected (by rw [tag];simp)
 have absent : cell∉group := fun h=>away cell h member
 have distinct : (cell::group).Nodup := List.nodup_cons.mpr ⟨absent,unique⟩
 have all : cell::group⊆final.boulders := List.cons_subset.mpr ⟨present,inside⟩
 have count := List.Nodup.length_le_of_subset distinct all
 have conservation := logged.trace.conservation
 have empty : final.holes=[] := completed
 rw [empty] at conservation
 change 18+0=final.boulders.length+16 at conservation
 simp only [List.length_cons] at count
 omega

theorem avoid : ∀i : Fin 3,∀c∈TightRowPairs11.pairs i,c∉([314,315,316,317] : List Cell) := by decide +kernel
theorem size : ∀i : Fin 3,(TightRowPairs11.pairs i).length=2 := by decide +kernel

theorem excluded {beforeDirs state beforePushes beforeMoves before dirs final pushes moves outcomes}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (tail : Logged soko1_1.board state dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : beforePushes+pushes≤327)
 (i : Fin 3) (inside : TightRowPairs11.pairs i⊆state.boulders) : False := by
 have persists := Owner1007.locked_trace (TightRowPairs11.locked i) tail.trace inside
 have unique := (List.nodup_append.mp (TightRowPairs11.unique i)).1
 have bound := other_capacity (first.append tail) completed cheap (TightRowPairs11.pairs i) unique persists (avoid i)
 rw [size i] at bound
 omega
#print axioms other_capacity
#print axioms excluded
end Owner1007.TightRowPairs32711
