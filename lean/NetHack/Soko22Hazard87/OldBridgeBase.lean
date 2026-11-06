import NetHack.Soko22Hazard87.AllSubExtra075
import NetHack.Sokoban22Refined85.Substitutions118
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
namespace Prior
end Prior
theorem prior_closed : NetHack.Sokoban22Refined85.support ⊆ ClosedComponents.soko2_2Support := by decide
theorem prior_bounded (c : Cell) (member : c ∈ NetHack.Sokoban22Refined85.support) : c < 10000 := by
  have checked : NetHack.Sokoban22Refined85.support.all (fun c => decide (c < 10000)) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp checked c member)
theorem prior_box_agree (p : Pattern) : Agree NetHack.Sokoban22Refined85.support (HazardPattern.boxes ClosedComponents.soko2_2Support p) p := by
  intro c member
  simp [HazardPattern.boxes, prior_closed member]
theorem prior_dummy : 10000 ∉ NetHack.Sokoban22Refined85.support := by decide
end NetHack.Soko22Hazard87
