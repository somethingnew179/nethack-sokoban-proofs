import NetHack.Soko22Hazard87.AllLocal
import NetHack.Sokoban22Refined85.LowerBound
import NetHack.Soko22Witness87.Soko22Macro87M238Solution
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def certificate : HazardPattern.Certificate soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential NetHack.Sokoban22Refined85.certificate where
  separator := 10000
  cells := ClosedComponents.soko2_2Support
  closed := ClosedSupport.check_sound _ _ ClosedComponents.soko2_2_closed_checked
  bounds := by
    intro cell member
    have checked : ClosedComponents.soko2_2Support.all (fun c => decide (c < 10000)) = true := by decide
    exact of_decide_eq_true (List.all_eq_true.mp checked cell member)
  bonus := bonus
  nonnegative := fun hero p => (bonus_range hero p).1
  localBound := allLocal
  goal := bonus_goal
theorem initial_good : HazardPattern.Good certificate soko2_2.initial := by decide +kernel
theorem initial_value : HazardPattern.value certificate soko2_2.initial = 87 := by
  unfold HazardPattern.value HazardPattern.correction
  rw [if_pos initial_good, NetHack.Sokoban22Refined85.initial_value]
  change 85 + bonus soko2_2.initial.player (HazardPattern.combined 10000 soko2_2.initial) = 87
  rw [initial_bonus]
  rfl
/-- Exact initial minimum lower half, restricted to the unchanged puzzle profile. -/
theorem pushes_lower_bound {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko2_2.board soko2_2.initial directions final pushes moves)
    (completed : Goal final) : 87 ≤ pushes :=
  pushes_minimal_of_potential (HazardPattern.stepBound certificate Generated.soko2_2_potential_valid)
    (HazardPattern.goalBound certificate Generated.soko2_2_potential_valid) 87 initial_value trace completed
theorem minimum87 :
    Trace soko2_2.board soko2_2.initial Generated.soko2_2Macro87M238Path Generated.soko2_2Macro87M238FinalState 87 238 ∧
    Goal Generated.soko2_2Macro87M238FinalState ∧
    (∀ directions final pushes moves, Trace soko2_2.board soko2_2.initial directions final pushes moves → Goal final → 87 ≤ pushes) :=
  ⟨Generated.soko2_2_macro87_m238_trace, Generated.soko2_2_macro87_m238_goal,
    fun _ _ _ _ trace completed => pushes_lower_bound trace completed⟩
end NetHack.Soko22Hazard87
