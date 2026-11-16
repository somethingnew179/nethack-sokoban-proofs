import NetHack.Sokoban.Reduction
import Owner1007.LockedTokens
import NetHack.Sokoban.Maps
namespace Owner1007.Upper133134Dead12
open NetHack.Sokoban NetHack.Sokoban.HazardPattern
open Owner1007 Owner1007.TokenAccounting
theorem locked : Locked soko1_2.board [108,133,134] :=
 locked_of_check _ _ (by decide +kernel)
theorem no_completion {state final dirs pushes moves history past pastMoves}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (inside : ([108,133,134]:List Cell)⊆state.boulders)
 (trace : Trace soko1_2.board state dirs final pushes moves)
 (completed : Goal final) :False := by
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 obtain ⟨outcomes,logged⟩ := log_exists trace actualUnique
 have kept := logged.locked_end_inside actualUnique [108,133,134] (by decide +kernel) inside
   [108,133,134] locked (fun _ h=>h)
 have endInside := logged.end_subset actualUnique [108,133,134] (by decide +kernel) inside
 have finalInside := List.Subset.trans kept endInside.2
 have count := List.Nodup.length_le_of_subset (by decide +kernel : ([108,133,134]:List Cell).Nodup) finalInside
 have conserved := (reached.append trace).conservation
 have empty : final.holes=[] := completed
 change 20+final.holes.length=final.boulders.length+18 at conserved
 rw [empty] at conserved
 simp only [List.length_nil] at conserved
 change 3≤final.boulders.length at count
 omega
#print axioms locked
#print axioms no_completion
end Owner1007.Upper133134Dead12
