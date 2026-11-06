/- Universal lower140 for the full original canonical soko3-2 start.
Existing group7 penalty5 and complementary raw credit1 use disjoint slack.
This is NOT a matching minimum or a new moves/full-game optimality claim. -/
import NetHack.Soko32Disjoint.Trace
namespace NetHack.Soko32Disjoint
open NetHack.Sokoban NetHack.Soko32Penalty5

theorem pushes_lower_bound {dirs : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko3_2.board soko3_2.initial dirs final pushes moves) (completed : Goal final) :
    140 ≤ pushes := by
  have unique : (initialGroup ++ complementary).Nodup :=
    initial_partition.nodup_iff.mpr (by decide +kernel)
  have subset : initialGroup ++ complementary ⊆ soko3_2.initial.boulders :=
    fun _ h => initial_partition.mem_iff.mp h
  have bound := trace_bound trace (Trace.nil soko3_2.initial) initialGroup complementary 5
    initial_ticket unique subset completed
  unfold combinedValue at bound
  rw [Generated.soko3_2_initial_potential,initial_top_bonus] at bound
  simp only [Int.ofNat_eq_natCast] at bound
  omega

end NetHack.Soko32Disjoint
