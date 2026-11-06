/- Raw nonlinear credit rows, independent of the full-state surplus.
A separate ghost argument is needed to assign disjoint push slack. -/
import NetHack.Sokoban.GhostProjection
import NetHack.Sokoban.PatternCorrection
namespace NetHack.Sokoban.RawPatternBonus
open PatternCorrection LowerBounds
set_option linter.unusedSimpArgs false

private theorem known_clear (support boxes : List Cell) (cell : Cell) (clear : cell ∉ boxes) :
    known support (project boxes) cell = false := by simp [known,project,clear]

private theorem corner_clear (board : Board) (support : List Cell) (state : State) (direction : Dir)
    (clear : cornerBlocked board state direction = false) :
    relaxedCorner board support (project state.boulders) state.player direction = false := by
  change HazardPattern.corner board (known support (project state.boulders)) state.player direction = false
  apply HeroPhasePotential.corner_clear_mono board _ (project state.boulders)
    (fun _ h => (Bool.and_eq_true_iff.mp h).2) state.player direction
  exact clear

theorem raw_step {board originalHoles potential} (cert : Certificate board originalHoles potential)
    (state : State) (unique : state.boulders.Nodup) (holesSubset : state.holes ⊆ originalHoles)
    (direction : Dir) (t : Transition) (checked : step board state direction = some t) :
    potential.value state + cert.bonus state.player (project state.boulders) ≤
      Int.ofNat t.pushCost + potential.value t.state + cert.bonus t.state.player (project t.state.boulders) := by
  have standing := step_player_clear board state direction t checked
  have playerClear := (step_player_clear _ _ _ _ checked).2.2.1
  have clear := known_clear cert.support state.boulders state.player playerClear
  have bound : potential.value state + cert.bonus state.player (project state.boulders) ≤
      Int.ofNat t.pushCost + potential.value t.state + cert.bonus t.state.player (project t.state.boulders) := by
    rcases step_cases_full _ _ _ _ checked with walk | pushed
    · rcases walk with ⟨target, adjacent, targetFloor, targetClear, _, shape⟩
      have corner := corner_clear board cert.support state direction (FiniteTopology.step_corner_clear _ _ _ _ checked)
      have targetKnown := known_clear cert.support state.boulders target targetClear
      have guard : walkGuard board cert.support (project state.boulders) state.player target direction = true := by
        simp only [walkGuard, clear, targetKnown, corner, Bool.not_false, Bool.true_and]
      have numeric := cert.walk state.player standing.1 direction target adjacent targetFloor _ guard
      subst t
      simpa only [Transition.pushCost, Bool.false_eq_true, ↓reduceIte, Int.ofNat_zero,
        Int.zero_add, Int.ofNat_eq_natCast, Potential.value, Int.add_le_add_iff_left] using Int.add_le_add_left numeric (potential.value state)
    · rcases pushed with ⟨source, result, adjacent, sourceFloor, present, pushed, shape⟩
      have diagonal : direction.diagonal = false := by
        cases hd : direction.diagonal with
        | false => rfl
        | true => simp [pushBoulder, hd] at pushed
      rcases NonlinearFacts.pushBoulder_first_clear _ _ _ _ _ pushed with
        ⟨first, firstAdj, firstFloor, _, firstClear⟩
      have firstKnown := known_clear cert.support state.boulders first firstClear
      have sourceGuard : (!cert.support.contains source || known cert.support (project state.boulders) source) = true := by
        simp [known, project, present]
      have landing : (!known cert.support (project state.boulders) result.landing || decide (result.landing = source)) = true := by
        rcases NonlinearFacts.pushBoulder_landing_old_clear_or_source _ _ _ _ _ pushed with same | fresh
        · simp [same]
        · simp [known_clear cert.support state.boulders result.landing fresh]
      have guard : pushGuard cert.support (project state.boulders) state.player source first result.landing = true := by
        simp only [pushGuard, clear, Bool.not_false, Bool.true_and, sourceGuard, firstKnown, landing, Bool.and_true]
      have boxes := weightSum_erase potential.boulder state.boulders source present
      rcases (pushBoulder_spec _ _ _ _ _ pushed).1 with stays | consumes
      · rcases stays with ⟨unfilled, resultBoxes⟩
        have numeric := cert.stay state.player standing.1 direction source first result.landing
          diagonal adjacent sourceFloor firstAdj firstFloor
          (PreciseRolling.push_no_fill_target _ _ _ _ _ pushed unfilled) _ guard
        rw [← project_replace state.boulders unique source result.landing, ← resultBoxes] at numeric
        subst t
        simp only [Transition.pushCost, ↓reduceIte, Int.ofNat_eq_natCast, Int.natCast_one, unfilled, afterFill,
          Potential.value, resultBoxes, weightSum] at numeric ⊢
        omega
      · rcases consumes with ⟨filled, hazard, resultBoxes⟩
        have numeric := cert.consume state.player standing.1 direction source first result.landing
          diagonal adjacent sourceFloor firstAdj firstFloor (pushBoulder_spec _ _ _ _ _ pushed).2
          (holesSubset hazard) _ guard
        rw [← project_erase state.boulders unique source, ← resultBoxes] at numeric
        have holes := weightSum_erase potential.hole state.holes result.landing hazard
        subst t
        simp only [Transition.pushCost, ↓reduceIte, Int.ofNat_eq_natCast, Int.natCast_one, filled, afterFill,
          Potential.value, resultBoxes] at numeric ⊢
        omega
  exact bound

theorem raw_goal {board originalHoles potential} (cert : Certificate board originalHoles potential)
    (valid : Valid board potential) (hero : Cell) (boxes : List Cell)
    (length : boxes.length ≤ cert.allowance) :
    cert.bonus hero (project boxes) ≤ weightSum (fun c => -potential.boulder c) boxes := by
  have count := NonlinearFacts.occupied_length_le cert.support boxes cert.unique
  have goal := cert.goal hero (project boxes) (Nat.le_trans count length)
  have bounded := NonlinearFacts.occupied_weightSum_le (fun c => -potential.boulder c)
    cert.support boxes (fun c => by have := valid.nonpositive c; omega) cert.unique
  exact Int.le_trans goal bounded

end NetHack.Sokoban.RawPatternBonus
