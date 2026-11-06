/- The full original Trace theorem follows only from ALL numeric checks
and the proved phase/coupling/oracle/mass reductions imported here. No new
Trace premise, push-graph metric, solver completeness or C-refinement axiom.
This source must be kernel compiled after Phase14All and Phase15All. -/
import NetHack.Soko11PairCandidate321.RemainingCertificate
import NetHack.Soko11PairCandidate321.Phase14All
import NetHack.Soko11PairCandidate321.Phase15All
namespace NetHack.Soko11PairCandidate321
open NetHack.Sokoban

theorem pushes_lower_bound {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko1_1.board soko1_1.initial directions final pushes moves) (completed : Goal final) :
    321 ≤ pushes :=
  lower321_of_last_two_fields all_positive_actions14 all_positive_environments14
    checked_full_mass_coverage15 all_excess_rows15 trace completed

theorem moves_lower_bound {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko1_1.board soko1_1.initial directions final pushes moves) (completed : Goal final) :
    321 ≤ moves := Nat.le_trans (pushes_lower_bound trace completed) (LowerBounds.trace_pushes_le_moves trace)

end NetHack.Soko11PairCandidate321
