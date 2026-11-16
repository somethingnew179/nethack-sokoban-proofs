import Owner1007.TightTailConsumed11
import Owner1007.LockedTokens
namespace Owner1007.TightRowPairs11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
def pairs (i : Fin 3) : List Cell := match i.val with |0=>[186,187]|1=>[187,188]|2=>[188,189]|_=>[]
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked : (List.finRange 3).all (fun i=>Owner1007.lockedCheck soko1_1.board (pairs i))=true := by decide +kernel
theorem locked (i : Fin 3) : Owner1007.Locked soko1_1.board (pairs i) :=
 Owner1007.locked_of_check _ _ (List.all_eq_true.mp checked i (by simp))
theorem unique (i : Fin 3) : (pairs i++[315,321]).Nodup := by
 obtain ⟨i,bound⟩ := i
 have choices : i=0∨i=1∨i=2 := by omega
 rcases choices with rfl|rfl|rfl <;> dsimp only [pairs] <;> decide +kernel
theorem nonempty (i : Fin 3) : pairs i≠[] := by
 obtain ⟨i,bound⟩ := i
 have choices : i=0∨i=1∨i=2 := by omega
 rcases choices with rfl|rfl|rfl <;> dsimp only [pairs] <;> decide +kernel
theorem excluded {beforeDirs state beforePushes beforeMoves before dirs final pushes moves outcomes}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (tail : Logged soko1_1.board state dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : beforePushes+pushes≤325)
 (i : Fin 3) (inside : pairs i⊆state.boulders) : False := by
 have gone := TightTailConsumed11.gone first tail completed cheap (pairs i) (unique i) inside
 have actualUnique := (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace).1
 have persists := tail.locked_end_inside actualUnique (pairs i) (List.nodup_append.mp (unique i)).1 inside
   (pairs i) (locked i) (List.Subset.refl _)
 have empty : pairs i=[] := List.eq_nil_iff_forall_not_mem.mpr (by
   intro c member
   have retained := persists member
   simpa only [gone,List.not_mem_nil] using retained)
 exact nonempty i empty
#print axioms checked
#print axioms excluded
end Owner1007.TightRowPairs11
