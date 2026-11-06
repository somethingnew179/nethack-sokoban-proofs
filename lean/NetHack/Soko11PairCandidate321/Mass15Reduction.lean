/- Exact exhaustive-coverage interface for the last phase. The external
114-pair exception list is NOT a hypothesis of an original Trace. -/
import NetHack.Soko11PairCandidate321.Mass15Data
import NetHack.Soko11PairCandidate321.ExcessFields
namespace NetHack.Soko11PairCandidate321
open NetHack.Sokoban NetHack.Sokoban.HazardPattern
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fullMassCoverage15 : Bool := (NetHack.Soko11Hero315.phases.crates 15).all massCoverageRow15

theorem covered_excess15_of_coverage (coverage : fullMassCoverage15 = true)
    (hero : Cell) (heroInside : hero ∈ NetHack.Soko11Hero315.phases.heroes 15)
    (group : List Cell) (unique : group.Nodup) (inside : group ⊆ NetHack.Soko11Hero315.phases.crates 15)
    (greater : massBasis.valueAt 15 hero group < valueAt 15 hero group) :
    ∃ pair ∈ excessPairs15, group.Perm pair := by
  have two := excess_implies_pair 15 hero group (by omega) greater
  cases group with
  | nil => simp at two
  | cons a tail =>
    cases tail with
    | nil => simp at two
    | cons b rest =>
      cases rest with
      | nil =>
        have different : a ≠ b := by simpa using (List.nodup_cons.mp unique).1
        have all := coverage
        unfold fullMassCoverage15 massCoverageRow15 at all
        have numeric := List.all_eq_true.mp (List.all_eq_true.mp all a (inside (by simp))) b (inside (by simp))
        unfold massPairCoverage15 at numeric
        by_cases matchPair : a = b ∨ [a,b] ∈ excessPairs15 ∨ [b,a] ∈ excessPairs15
        · rcases matchPair with same|forward|backward
          · exact False.elim (different same)
          · exact ⟨[a,b],forward,List.Perm.refl _⟩
          · exact ⟨[b,a],backward,List.Perm.swap b a []⟩
        · by_cases zero : lookup (tables 15) (code [a,b]) = 0
          · have bit : bonus 15 hero [a,b] = 0 := by simp [bonus,zero]
            have positive := excess_implies_positive 15 hero [a,b] (by omega) greater
            rw [bit] at positive
            omega
          · simp only [if_neg matchPair,if_neg zero] at numeric
            have inequality := of_decide_eq_true (List.all_eq_true.mp numeric hero heroInside)
            omega
      | cons c rest => simp only [List.length_cons] at two; omega

theorem excess_actions15_of_coverage_rows (coverage : fullMassCoverage15 = true)
    (rows : excessPairs15.all (rowCheck 15) = true) : ExcessActionsAt 15 := by
  intro hero heroInside group unique inside length floor door hole clear greater direction outcome oracle
  rcases covered_excess15_of_coverage coverage hero heroInside group unique inside greater with ⟨pair,member,related⟩
  have checked := List.all_eq_true.mp rows pair member
  have projection : PatternCorrection.project group = PatternCorrection.project pair :=
    funext fun _ => related.contains_eq
  have other : stepOracle soko1_1.board (PatternCorrection.project pair)
      (PatternCorrection.project (soko1_1.initial.holes.drop 15)) hero direction = some outcome := by
    rw [←projection]
    exact oracle
  exact (localBound_respects 15 hero group pair related outcome).mpr
    (rowCheck_actions 15 pair checked hero heroInside direction outcome other)

theorem excess_environments15_of_coverage_rows (coverage : fullMassCoverage15 = true)
    (rows : excessPairs15.all (rowCheck 15) = true) : ExcessEnvironmentsAt 15 := by
  intro hero heroInside group unique inside nextInside length floor door hole clear greater
  rcases covered_excess15_of_coverage coverage hero heroInside group unique inside greater with ⟨pair,member,related⟩
  have checked := List.all_eq_true.mp rows pair member
  have otherClear : hero ∉ pair := fun h => clear (related.mem_iff.mpr h)
  rw [valueAt_respects 15 hero group pair related,valueAt_respects 16 hero group pair related]
  exact rowCheck_environment 15 pair checked hero heroInside otherClear (by decide)

end NetHack.Soko11PairCandidate321
