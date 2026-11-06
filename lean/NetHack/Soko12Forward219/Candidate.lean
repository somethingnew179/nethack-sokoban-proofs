/- Candidate on the full original map/profile. Initial/goal arithmetic is
insufficient: the universal local phase0 inequalities are still required. -/
import NetHack.Soko12Forward219.Shared.OldBridge
import NetHack.Sokoban12CostPartition.LowerBound
import NetHack.SokobanLinearPhases.Map12.Invariant
import NetHack.Sokoban.HazardPhaseCountedCorrection

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward219.Candidate
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
open NetHack.Sokoban.HazardPhaseCountedCorrection

def value (s : State) : Int :=
  PatternCorrection.value NetHack.Sokoban12CostPartition.certificate s +
    if Good NetHack.Sokoban12CostPartition.certificate
        NetHack.SokobanLinearPhases.Map12.certificate s then
      DecisionDAG.eval Shared.read (project s.boulders)
        (Shared.gamma (phaseOf soko1_2.initial.holes s) s.player)
    else 0

theorem initial_value : value soko1_2.initial = 219 := by decide +kernel

theorem goal_bound (s : State) (completed : Goal s) : value s ≤ 0 := by
  have base := PatternCorrection.goalBound NetHack.Sokoban12CostPartition.certificate
    Generated.soko1_2_potential_valid s completed
  have empty : s.holes = [] := completed
  have phase : phaseOf soko1_2.initial.holes s ≠ 0 := by
    simp only [phaseOf, empty, List.length_nil, Nat.sub_zero]
    decide +kernel
  have gamma_zero : Shared.gamma (phaseOf soko1_2.initial.holes s) s.player = 0 := by
    simp only [Shared.gamma, if_neg phase]
  have zero : DecisionDAG.eval Shared.read (project s.boulders) 0 = 0 :=
    DecisionDAG.eval_literal (by decide +kernel) _
  unfold value
  split
  · rw [gamma_zero, zero, Int.add_zero]
    exact base
  · simpa only [Int.add_zero] using base

end NetHack.Soko12Forward219.Candidate
