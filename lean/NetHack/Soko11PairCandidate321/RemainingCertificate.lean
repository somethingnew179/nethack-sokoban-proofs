/- The remaining certificate obligations after proved phase0, exact
interior transfer and last-fill mass reduction. Still conditional until the
phase14 and phase15 finite checks are all supplied. -/
import NetHack.Soko11PairCandidate321.Phase00All
import NetHack.Soko11PairCandidate321.InteriorTransfer
import NetHack.Soko11PairCandidate321.Mass15Reduction
namespace NetHack.Soko11PairCandidate321
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem actions_of_last_two_fields (actions14 : PositiveActionsAt 14)
    (coverage15 : fullMassCoverage15 = true) (rows15 : excessPairs15.all (rowCheck 15) = true) :
    AllExcessActions := by
  intro phase active hero heroInside group unique inside length floor door hole clear greater direction outcome oracle
  have active16 : phase < 16 := active
  by_cases first : phase = 0
  · subst phase
    exact all_positive_actions00 hero heroInside group unique inside
      (excess_implies_positive 0 hero group (by omega) greater) direction outcome oracle
  · by_cases last : phase = 15
    · subst phase
      exact excess_actions15_of_coverage_rows coverage15 rows15 hero heroInside group unique inside length
        floor door hole clear greater direction outcome oracle
    · exact interior_actions_from14 actions14 phase (by omega) (by omega) hero heroInside group unique inside
        length floor door hole clear (excess_implies_positive phase hero group (by omega) greater) direction outcome oracle

theorem environments_of_last_two_fields (environments14 : PositiveEnvironmentsAt 14)
    (coverage15 : fullMassCoverage15 = true) (rows15 : excessPairs15.all (rowCheck 15) = true) :
    AllExcessEnvironments := by
  intro phase active hero heroInside group unique inside nextInside length floor door hole clear greater
  have active16 : phase < 16 := active
  by_cases first : phase = 0
  · subst phase
    exact all_positive_environments00 hero heroInside group unique inside clear
      (excess_implies_positive 0 hero group (by omega) greater)
  · by_cases last : phase = 15
    · subst phase
      exact excess_environments15_of_coverage_rows coverage15 rows15 hero heroInside group unique inside nextInside
        length floor door hole clear greater
    · exact interior_environments_from14 environments14 phase (by omega) (by omega) hero heroInside group unique inside
        nextInside length floor door hole clear (excess_implies_positive phase hero group (by omega) greater)

theorem lower321_of_last_two_fields (actions14 : PositiveActionsAt 14) (environments14 : PositiveEnvironmentsAt 14)
    (coverage15 : fullMassCoverage15 = true) (rows15 : excessPairs15.all (rowCheck 15) = true)
    {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko1_1.board soko1_1.initial directions final pushes moves) (completed : Goal final) :
    321 ≤ pushes :=
  lower321_of_all_excess_rows (actions_of_last_two_fields actions14 coverage15 rows15)
    (environments_of_last_two_fields environments14 coverage15 rows15) trace completed

end NetHack.Soko11PairCandidate321
