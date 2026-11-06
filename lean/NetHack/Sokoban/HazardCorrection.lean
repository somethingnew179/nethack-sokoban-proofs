/- A nonnegative, hazard-aware correction over a previously proved potential.
Only invariant-derived guards are used. Neither solver reachability nor a
smaller collection of player actions is a premise of the lower bound. -/
import NetHack.Sokoban.HazardPattern

set_option linter.unusedSimpArgs false
namespace NetHack.Sokoban.HazardPattern
open PatternCorrection LowerBounds

structure Certificate (board : Board) (original : List Cell) (potential : Potential)
    (prior : PatternCorrection.Certificate board original potential) where
  separator : Nat
  cells : List Cell
  closed : ClosedSupport.Closed board cells
  bounds : ∀ cell ∈ cells, cell < separator
  bonus : Cell → Pattern → Int
  nonnegative : ∀ hero pattern, 0 ≤ bonus hero pattern
  localBound : ∀ hero, hero ∈ board.floor → ∀ direction pattern outcome,
    stepOracle board (boxes cells pattern) (hazards separator original pattern)
      hero direction = some outcome →
    bonus (nextHero outcome) (afterPattern separator pattern outcome) < bonus hero pattern →
    prior.bonus hero (boxes cells pattern) + bonus hero pattern ≤
      slack potential outcome +
        prior.bonus (nextHero outcome) (boxes cells (afterPattern separator pattern outcome)) +
        bonus (nextHero outcome) (afterPattern separator pattern outcome)
  goal : ∀ hero pattern, (∀ hole ∈ original, pattern (separator + hole) = false) → bonus hero pattern = 0

def Good {board original potential prior} (cert : Certificate board original potential prior)
    (state : State) : Prop :=
  PatternCorrection.Good board original prior.allowance state ∧
    state.holes.Nodup ∧ ClosedSupport.Within cert.cells state

instance {board original potential prior} (cert : Certificate board original potential prior)
    (state : State) : Decidable (Good cert state) := by unfold Good; infer_instance

def correction {board original potential prior} (cert : Certificate board original potential prior)
    (state : State) : Int :=
  if Good cert state then cert.bonus state.player (combined cert.separator state) else 0

def value {board original potential prior} (cert : Certificate board original potential prior)
    (state : State) : Int := PatternCorrection.value prior state + correction cert state

theorem correction_nonnegative {board original potential prior}
    (cert : Certificate board original potential prior) (state : State) : 0 ≤ correction cert state := by
  unfold correction
  split
  · exact cert.nonnegative _ _
  · omega

theorem step_good {board original potential prior} (cert : Certificate board original potential prior)
    (state : State) (direction : Dir) (t : Transition) (good : Good cert state)
    (checked : step board state direction = some t) : Good cert t.state := by
  exact ⟨PatternCorrection.step_good _ _ _ _ _ _ good.1 checked,
    good.2.1.sublist (step_holes_sublist _ _ _ _ checked),
    ClosedSupport.step_within _ _ cert.closed _ _ _ good.2.2 checked⟩

theorem stepBound {board original potential prior} (cert : Certificate board original potential prior)
    (valid : Valid board potential) : StepBound board (value cert) := by
  intro state direction t checked
  have baseline := PatternCorrection.stepBound prior valid state direction t checked
  have afterNonnegative := correction_nonnegative cert t.state
  by_cases good : Good cert state
  · have nextGood := step_good cert state direction t good checked
    by_cases decreasing : cert.bonus t.state.player (combined cert.separator t.state) <
        cert.bonus state.player (combined cert.separator state)
    · have beforeBoxes := boxes_combined cert.separator cert.cells state cert.bounds good.2.2.2
      have beforeHoles := hazards_combined cert.separator original state good.1.2.1
      rcases stepOracle_covers board state good.1.1 direction t checked with ⟨outcome, oracle, effect⟩
      have oracleExact : stepOracle board (boxes cert.cells (combined cert.separator state))
          (hazards cert.separator original (combined cert.separator state)) state.player direction = some outcome := by
        simpa only [beforeBoxes, beforeHoles] using oracle
      have patternExact := combined_matches cert.separator cert.cells cert.bounds state t outcome
        good.1.1 good.2.1 good.2.2.2 nextGood.2.2.2 effect
      have heroExact := matches_hero state t outcome effect
      have decreases : cert.bonus (nextHero outcome)
          (afterPattern cert.separator (combined cert.separator state) outcome) <
          cert.bonus state.player (combined cert.separator state) := by
        simpa only [← patternExact, ← heroExact] using decreasing
      have numeric := cert.localBound state.player good.1.2.2.1 direction _ outcome oracleExact decreases
      have afterBoxes := boxes_combined cert.separator cert.cells t.state cert.bounds nextGood.2.2.2
      rw [beforeBoxes, ← patternExact, ← heroExact, afterBoxes] at numeric
      have delta := matches_delta potential state t outcome effect
      simp only [value, correction, if_pos good, if_pos nextGood,
        PatternCorrection.value, PatternCorrection.correction, if_pos good.1, if_pos nextGood.1]
      omega
    · simp only [value, correction, if_pos good, if_pos nextGood]
      omega
  · simp only [value, correction, if_neg good]
    change PatternCorrection.value prior state + 0 ≤ Int.ofNat t.pushCost +
      (PatternCorrection.value prior t.state + correction cert t.state)
    omega

theorem goalBound {board original potential prior} (cert : Certificate board original potential prior)
    (valid : Valid board potential) (state : State) (completed : Goal state) : value cert state ≤ 0 := by
  have baseline := PatternCorrection.goalBound prior valid state completed
  have empty : state.holes = [] := completed
  have zero := cert.goal state.player (combined cert.separator state) (by
    intro hole member
    simp [combined, empty, show ¬cert.separator + hole < cert.separator by omega])
  by_cases good : Good cert state <;> simpa only [value, correction, good, ↓reduceIte, zero, Int.add_zero] using baseline

end NetHack.Sokoban.HazardPattern
