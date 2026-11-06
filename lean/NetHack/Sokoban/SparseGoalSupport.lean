/- Safe terminal credit for a projection containing the prior bonus support.
Negative-weight cells outside the projection may be forgotten: their credit
is nonnegative. This is a generic proof, not a new numerical map instance. -/
import NetHack.Sokoban.WeightedGoal
import NetHack.Sokoban.CountedLocalCase
import NetHack.Sokoban.PatternCorrection
namespace NetHack.Sokoban.SparseGoalSupport
open LowerBounds

theorem bonus_goal {board original potential}
    (prior : PatternCorrection.Certificate board original potential)
    (valid : Valid board potential) (selected : List Cell)
    (contains : prior.support.Sublist selected) (hero : Cell) (p : PatternCorrection.Pattern)
    (budget : (selected.filter p).length ≤ prior.allowance) :
    prior.bonus hero p ≤ weightSum (fun cell => -potential.boulder cell) (selected.filter p) := by
  have smaller := DecisionDAGCountedCompact.count_sublist contains p
  rw [CountedLocalCase.count_eq_mass prior.support p,
    CountedLocalCase.count_eq_mass selected p] at smaller
  change Int.ofNat (prior.support.filter p).length ≤ Int.ofNat (selected.filter p).length at smaller
  simp only [Int.ofNat_eq_natCast] at smaller
  have available : (prior.support.filter p).length ≤ prior.allowance := by omega
  have base := prior.goal hero p available
  have cost := WeightedGoal.sum_sublist (fun cell => -potential.boulder cell)
    (fun cell => Int.neg_nonneg.mpr (valid.nonpositive cell)) contains p
  rw [WeightedGoal.sum_eq_weightSum _ prior.support p,
    WeightedGoal.sum_eq_weightSum _ selected p] at cost
  omega

def terminalCut {board original potential}
    (prior : PatternCorrection.Certificate board original potential)
    (selected : List Cell) (hero : Cell) (p : PatternCorrection.Pattern) : Int :=
  if prior.bonus hero p = WeightedGoal.sum (fun cell => -potential.boulder cell) selected p then 0 else 1

theorem terminalCut_goal {board original potential}
    (prior : PatternCorrection.Certificate board original potential)
    (valid : Valid board potential) (selected : List Cell)
    (contains : prior.support.Sublist selected) (hero : Cell) (p : PatternCorrection.Pattern)
    (budget : (selected.filter p).length ≤ prior.allowance) :
    prior.bonus hero p + terminalCut prior selected hero p ≤
      WeightedGoal.sum (fun cell => -potential.boulder cell) selected p := by
  have base := bonus_goal prior valid selected contains hero p budget
  rw [← WeightedGoal.sum_eq_weightSum] at base
  by_cases tight : prior.bonus hero p = WeightedGoal.sum (fun cell => -potential.boulder cell) selected p
  · simp only [terminalCut,if_pos tight]
    omega
  · simp only [terminalCut,if_neg tight]
    omega
end NetHack.Sokoban.SparseGoalSupport
