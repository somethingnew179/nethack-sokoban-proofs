import NetHack.Soko22Hazard87.OldAfter012
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
namespace Prior
end Prior
theorem oldAfter1040 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 256 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 256 (.stay 255)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at256]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 256 (.stay 255))))]
  change NetHack.Sokoban22Refined85.d3224 (change p 256 (some 255)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 256 (some 255) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter1041 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 259 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 259))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at259]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 259)))]
  change NetHack.Sokoban22Refined85.d3224 p = _
  exact oldNode3224 p
theorem oldAfter1042 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 259 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 259 (.fill 260)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at259]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 259 (.fill 260))))]
  have hazardsIgnored : Agree NetHack.Sokoban22Refined85.support (HazardPattern.afterPattern 10000 p (.push 259 (.fill 260))) (change p 259 none) := by
    intro c member
    have bound := prior_bounded c member
    have ne : 10000 + 260 ≠ c := by simp only [Cell] at *; omega
    simp [HazardPattern.afterPattern, change, ne]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ hazardsIgnored]
  have representative := change_representative NetHack.Sokoban22Refined85.support p 259 none 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter1043 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 259 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 259 (.stay 260)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at259]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 259 (.stay 260))))]
  change NetHack.Sokoban22Refined85.d3224 (change p 259 (some 260)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 259 (some 260) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter1044 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 257 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 257))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at257]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 257)))]
  change NetHack.Sokoban22Refined85.d3224 p = _
  exact oldNode3224 p
theorem oldAfter1045 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 257 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 257 (.fill 256)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at257]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 257 (.fill 256))))]
  have hazardsIgnored : Agree NetHack.Sokoban22Refined85.support (HazardPattern.afterPattern 10000 p (.push 257 (.fill 256))) (change p 257 none) := by
    intro c member
    have bound := prior_bounded c member
    have ne : 10000 + 256 ≠ c := by simp only [Cell] at *; omega
    simp [HazardPattern.afterPattern, change, ne]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ hazardsIgnored]
  have representative := change_representative NetHack.Sokoban22Refined85.support p 257 none 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter1046 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 257 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 257 (.stay 256)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at257]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 257 (.stay 256))))]
  change NetHack.Sokoban22Refined85.d3224 (change p 257 (some 256)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 257 (some 256) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter1047 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 260 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 260))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at260]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 260)))]
  change NetHack.Sokoban22Refined85.d3224 p = _
  exact oldNode3224 p
theorem oldAfter1048 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 258 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 258))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at258]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 258)))]
  change NetHack.Sokoban22Refined85.d3224 p = _
  exact oldNode3224 p
theorem oldAfter1049 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 258 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 258 (.fill 257)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at258]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 258 (.fill 257))))]
  have hazardsIgnored : Agree NetHack.Sokoban22Refined85.support (HazardPattern.afterPattern 10000 p (.push 258 (.fill 257))) (change p 258 none) := by
    intro c member
    have bound := prior_bounded c member
    have ne : 10000 + 257 ≠ c := by simp only [Cell] at *; omega
    simp [HazardPattern.afterPattern, change, ne]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ hazardsIgnored]
  have representative := change_representative NetHack.Sokoban22Refined85.support p 258 none 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter1050 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 258 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 258 (.stay 257)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at258]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 258 (.stay 257))))]
  change NetHack.Sokoban22Refined85.d3224 (change p 258 (some 257)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 258 (some 257) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter1051 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 259 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 259))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at259]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 259)))]
  change NetHack.Sokoban22Refined85.d3224 p = _
  exact oldNode3224 p
theorem oldAfter1052 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 259 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 259 (.fill 258)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at259]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 259 (.fill 258))))]
  have hazardsIgnored : Agree NetHack.Sokoban22Refined85.support (HazardPattern.afterPattern 10000 p (.push 259 (.fill 258))) (change p 259 none) := by
    intro c member
    have bound := prior_bounded c member
    have ne : 10000 + 258 ≠ c := by simp only [Cell] at *; omega
    simp [HazardPattern.afterPattern, change, ne]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ hazardsIgnored]
  have representative := change_representative NetHack.Sokoban22Refined85.support p 259 none 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter1053 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 259 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 259 (.stay 258)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at259]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 259 (.stay 258))))]
  change NetHack.Sokoban22Refined85.d3224 (change p 259 (some 258)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 259 (some 258) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter1054 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 240 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 240))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at240]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 240)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter1055 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 240 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 240 (.stay 218)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at240]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 240 (.stay 218))))]
  change NetHack.Sokoban22Refined85.d0 (change p 240 (some 218)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 240 (some 218) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
end NetHack.Soko22Hazard87
