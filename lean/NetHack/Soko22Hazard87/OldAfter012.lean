import NetHack.Soko22Hazard87.OldAfter011
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
namespace Prior
end Prior
theorem oldAfter960 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 247 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 247 (.stay 248)))) = d351900 p := by
  rw [NetHack.Sokoban22Refined85.at247]
  rw [NetHack.Sokoban22Refined85.agree4036 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 247 (.stay 248))))]
  change NetHack.Sokoban22Refined85.d4036 (change p 247 (some 248)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 247 (some 248) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree4036 _ _ representative]
  change NetHack.Sokoban22Refined85.d4036 (change p 247 none) = _
  rw [NetHack.Sokoban22Refined85.sub12287]
  exact oldNode7013 p
theorem oldAfter961 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 245 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 245))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at245]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 245)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter962 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 225 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 225))) = d50493 p := by
  rw [NetHack.Sokoban22Refined85.at225]
  rw [NetHack.Sokoban22Refined85.agree2894 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 225)))]
  change NetHack.Sokoban22Refined85.d2894 p = _
  exact oldNode2894 p
theorem oldAfter963 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 223 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 223))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at223]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 223)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter964 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 225 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 225))) = d50493 p := by
  rw [NetHack.Sokoban22Refined85.at225]
  rw [NetHack.Sokoban22Refined85.agree2894 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 225)))]
  change NetHack.Sokoban22Refined85.d2894 p = _
  exact oldNode2894 p
theorem oldAfter965 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 248 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 248))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at248]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 248)))]
  change NetHack.Sokoban22Refined85.d3224 p = _
  exact oldNode3224 p
theorem oldAfter966 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 248 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 248 (.fill 250)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at248]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 248 (.fill 250))))]
  have hazardsIgnored : Agree NetHack.Sokoban22Refined85.support (HazardPattern.afterPattern 10000 p (.push 248 (.fill 250))) (change p 248 none) := by
    intro c member
    have bound := prior_bounded c member
    have ne : 10000 + 250 ≠ c := by simp only [Cell] at *; omega
    simp [HazardPattern.afterPattern, change, ne]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ hazardsIgnored]
  have representative := change_representative NetHack.Sokoban22Refined85.support p 248 none 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter967 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 248 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 248 (.fill 251)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at248]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 248 (.fill 251))))]
  have hazardsIgnored : Agree NetHack.Sokoban22Refined85.support (HazardPattern.afterPattern 10000 p (.push 248 (.fill 251))) (change p 248 none) := by
    intro c member
    have bound := prior_bounded c member
    have ne : 10000 + 251 ≠ c := by simp only [Cell] at *; omega
    simp [HazardPattern.afterPattern, change, ne]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ hazardsIgnored]
  have representative := change_representative NetHack.Sokoban22Refined85.support p 248 none 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter968 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 248 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 248 (.fill 252)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at248]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 248 (.fill 252))))]
  have hazardsIgnored : Agree NetHack.Sokoban22Refined85.support (HazardPattern.afterPattern 10000 p (.push 248 (.fill 252))) (change p 248 none) := by
    intro c member
    have bound := prior_bounded c member
    have ne : 10000 + 252 ≠ c := by simp only [Cell] at *; omega
    simp [HazardPattern.afterPattern, change, ne]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ hazardsIgnored]
  have representative := change_representative NetHack.Sokoban22Refined85.support p 248 none 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter969 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 248 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 248 (.fill 253)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at248]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 248 (.fill 253))))]
  have hazardsIgnored : Agree NetHack.Sokoban22Refined85.support (HazardPattern.afterPattern 10000 p (.push 248 (.fill 253))) (change p 248 none) := by
    intro c member
    have bound := prior_bounded c member
    have ne : 10000 + 253 ≠ c := by simp only [Cell] at *; omega
    simp [HazardPattern.afterPattern, change, ne]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ hazardsIgnored]
  have representative := change_representative NetHack.Sokoban22Refined85.support p 248 none 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter970 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 248 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 248 (.fill 254)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at248]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 248 (.fill 254))))]
  have hazardsIgnored : Agree NetHack.Sokoban22Refined85.support (HazardPattern.afterPattern 10000 p (.push 248 (.fill 254))) (change p 248 none) := by
    intro c member
    have bound := prior_bounded c member
    have ne : 10000 + 254 ≠ c := by simp only [Cell] at *; omega
    simp [HazardPattern.afterPattern, change, ne]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ hazardsIgnored]
  have representative := change_representative NetHack.Sokoban22Refined85.support p 248 none 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter971 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 248 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 248 (.fill 255)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at248]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 248 (.fill 255))))]
  have hazardsIgnored : Agree NetHack.Sokoban22Refined85.support (HazardPattern.afterPattern 10000 p (.push 248 (.fill 255))) (change p 248 none) := by
    intro c member
    have bound := prior_bounded c member
    have ne : 10000 + 255 ≠ c := by simp only [Cell] at *; omega
    simp [HazardPattern.afterPattern, change, ne]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ hazardsIgnored]
  have representative := change_representative NetHack.Sokoban22Refined85.support p 248 none 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter972 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 248 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 248 (.fill 256)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at248]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 248 (.fill 256))))]
  have hazardsIgnored : Agree NetHack.Sokoban22Refined85.support (HazardPattern.afterPattern 10000 p (.push 248 (.fill 256))) (change p 248 none) := by
    intro c member
    have bound := prior_bounded c member
    have ne : 10000 + 256 ≠ c := by simp only [Cell] at *; omega
    simp [HazardPattern.afterPattern, change, ne]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ hazardsIgnored]
  have representative := change_representative NetHack.Sokoban22Refined85.support p 248 none 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter973 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 248 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 248 (.fill 257)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at248]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 248 (.fill 257))))]
  have hazardsIgnored : Agree NetHack.Sokoban22Refined85.support (HazardPattern.afterPattern 10000 p (.push 248 (.fill 257))) (change p 248 none) := by
    intro c member
    have bound := prior_bounded c member
    have ne : 10000 + 257 ≠ c := by simp only [Cell] at *; omega
    simp [HazardPattern.afterPattern, change, ne]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ hazardsIgnored]
  have representative := change_representative NetHack.Sokoban22Refined85.support p 248 none 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter974 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 248 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 248 (.fill 258)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at248]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 248 (.fill 258))))]
  have hazardsIgnored : Agree NetHack.Sokoban22Refined85.support (HazardPattern.afterPattern 10000 p (.push 248 (.fill 258))) (change p 248 none) := by
    intro c member
    have bound := prior_bounded c member
    have ne : 10000 + 258 ≠ c := by simp only [Cell] at *; omega
    simp [HazardPattern.afterPattern, change, ne]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ hazardsIgnored]
  have representative := change_representative NetHack.Sokoban22Refined85.support p 248 none 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter975 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 248 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 248 (.fill 259)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at248]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 248 (.fill 259))))]
  have hazardsIgnored : Agree NetHack.Sokoban22Refined85.support (HazardPattern.afterPattern 10000 p (.push 248 (.fill 259))) (change p 248 none) := by
    intro c member
    have bound := prior_bounded c member
    have ne : 10000 + 259 ≠ c := by simp only [Cell] at *; omega
    simp [HazardPattern.afterPattern, change, ne]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ hazardsIgnored]
  have representative := change_representative NetHack.Sokoban22Refined85.support p 248 none 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter976 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 248 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 248 (.fill 260)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at248]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 248 (.fill 260))))]
  have hazardsIgnored : Agree NetHack.Sokoban22Refined85.support (HazardPattern.afterPattern 10000 p (.push 248 (.fill 260))) (change p 248 none) := by
    intro c member
    have bound := prior_bounded c member
    have ne : 10000 + 260 ≠ c := by simp only [Cell] at *; omega
    simp [HazardPattern.afterPattern, change, ne]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ hazardsIgnored]
  have representative := change_representative NetHack.Sokoban22Refined85.support p 248 none 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter977 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 246 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 246))) = d51138 p := by
  rw [NetHack.Sokoban22Refined85.at246]
  rw [NetHack.Sokoban22Refined85.agree3539 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 246)))]
  change NetHack.Sokoban22Refined85.d3539 p = _
  exact oldNode3539 p
theorem oldAfter978 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 246 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 246 (.stay 245)))) = d338883 p := by
  rw [NetHack.Sokoban22Refined85.at246]
  rw [NetHack.Sokoban22Refined85.agree3539 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 246 (.stay 245))))]
  change NetHack.Sokoban22Refined85.d3539 (change p 246 (some 245)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 246 (some 245) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3539 _ _ representative]
  change NetHack.Sokoban22Refined85.d3539 (change p 246 none) = _
  rw [NetHack.Sokoban22Refined85.sub12615]
  exact oldNode6557 p
theorem oldAfter979 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 226 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 226))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at226]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 226)))]
  change NetHack.Sokoban22Refined85.d3224 p = _
  exact oldNode3224 p
theorem oldAfter980 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 224 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 224))) = d50101 p := by
  rw [NetHack.Sokoban22Refined85.at224]
  rw [NetHack.Sokoban22Refined85.agree2502 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 224)))]
  change NetHack.Sokoban22Refined85.d2502 p = _
  exact oldNode2502 p
theorem oldAfter981 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 226 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 226))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at226]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 226)))]
  change NetHack.Sokoban22Refined85.d3224 p = _
  exact oldNode3224 p
theorem oldAfter982 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 226 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 226 (.stay 204)))) = d367985 p := by
  rw [NetHack.Sokoban22Refined85.at226]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 226 (.stay 204))))]
  change NetHack.Sokoban22Refined85.d3224 (change p 226 (some 204)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 226 (some 204) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 (some 204)) = _
  rw [NetHack.Sokoban22Refined85.sub13118]
  exact oldNode7244 p
theorem oldAfter983 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 249 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 249))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at249]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 249)))]
  change NetHack.Sokoban22Refined85.d3224 p = _
  exact oldNode3224 p
theorem oldAfter984 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 249 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 249 (.fill 250)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at249]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 249 (.fill 250))))]
  have hazardsIgnored : Agree NetHack.Sokoban22Refined85.support (HazardPattern.afterPattern 10000 p (.push 249 (.fill 250))) (change p 249 none) := by
    intro c member
    have bound := prior_bounded c member
    have ne : 10000 + 250 ≠ c := by simp only [Cell] at *; omega
    simp [HazardPattern.afterPattern, change, ne]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ hazardsIgnored]
  have representative := change_representative NetHack.Sokoban22Refined85.support p 249 none 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter985 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 249 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 249 (.stay 250)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at249]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 249 (.stay 250))))]
  change NetHack.Sokoban22Refined85.d3224 (change p 249 (some 250)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 249 (some 250) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter986 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 247 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 247))) = d51635 p := by
  rw [NetHack.Sokoban22Refined85.at247]
  rw [NetHack.Sokoban22Refined85.agree4036 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 247)))]
  change NetHack.Sokoban22Refined85.d4036 p = _
  exact oldNode4036 p
theorem oldAfter987 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 247 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 247 (.stay 246)))) = d371353 p := by
  rw [NetHack.Sokoban22Refined85.at247]
  rw [NetHack.Sokoban22Refined85.agree4036 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 247 (.stay 246))))]
  change NetHack.Sokoban22Refined85.d4036 (change p 247 (some 246)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 247 (some 246) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree4036 _ _ representative]
  change NetHack.Sokoban22Refined85.d4036 (change p 247 (some 246)) = _
  rw [NetHack.Sokoban22Refined85.sub13652]
  exact oldNode7661 p
theorem oldAfter988 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 225 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 225))) = d50493 p := by
  rw [NetHack.Sokoban22Refined85.at225]
  rw [NetHack.Sokoban22Refined85.agree2894 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 225)))]
  change NetHack.Sokoban22Refined85.d2894 p = _
  exact oldNode2894 p
theorem oldAfter989 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 250 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 250))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at250]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 250)))]
  change NetHack.Sokoban22Refined85.d3224 p = _
  exact oldNode3224 p
theorem oldAfter990 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 250 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 250 (.fill 251)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at250]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 250 (.fill 251))))]
  have hazardsIgnored : Agree NetHack.Sokoban22Refined85.support (HazardPattern.afterPattern 10000 p (.push 250 (.fill 251))) (change p 250 none) := by
    intro c member
    have bound := prior_bounded c member
    have ne : 10000 + 251 ≠ c := by simp only [Cell] at *; omega
    simp [HazardPattern.afterPattern, change, ne]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ hazardsIgnored]
  have representative := change_representative NetHack.Sokoban22Refined85.support p 250 none 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter991 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 250 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 250 (.stay 251)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at250]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 250 (.stay 251))))]
  change NetHack.Sokoban22Refined85.d3224 (change p 250 (some 251)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 250 (some 251) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter992 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 248 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 248))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at248]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 248)))]
  change NetHack.Sokoban22Refined85.d3224 p = _
  exact oldNode3224 p
theorem oldAfter993 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 248 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 248 (.stay 247)))) = d376289 p := by
  rw [NetHack.Sokoban22Refined85.at248]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 248 (.stay 247))))]
  change NetHack.Sokoban22Refined85.d3224 (change p 248 (some 247)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 248 (some 247) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 (some 247)) = _
  rw [NetHack.Sokoban22Refined85.sub14191]
  exact oldNode8083 p
theorem oldAfter994 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 226 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 226))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at226]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 226)))]
  change NetHack.Sokoban22Refined85.d3224 p = _
  exact oldNode3224 p
theorem oldAfter995 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 251 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 251))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at251]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 251)))]
  change NetHack.Sokoban22Refined85.d3224 p = _
  exact oldNode3224 p
theorem oldAfter996 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 251 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 251 (.fill 252)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at251]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 251 (.fill 252))))]
  have hazardsIgnored : Agree NetHack.Sokoban22Refined85.support (HazardPattern.afterPattern 10000 p (.push 251 (.fill 252))) (change p 251 none) := by
    intro c member
    have bound := prior_bounded c member
    have ne : 10000 + 252 ≠ c := by simp only [Cell] at *; omega
    simp [HazardPattern.afterPattern, change, ne]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ hazardsIgnored]
  have representative := change_representative NetHack.Sokoban22Refined85.support p 251 none 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter997 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 251 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 251 (.stay 252)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at251]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 251 (.stay 252))))]
  change NetHack.Sokoban22Refined85.d3224 (change p 251 (some 252)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 251 (some 252) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter998 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 249 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 249))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at249]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 249)))]
  change NetHack.Sokoban22Refined85.d3224 p = _
  exact oldNode3224 p
theorem oldAfter999 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 249 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 249 (.stay 248)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at249]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 249 (.stay 248))))]
  change NetHack.Sokoban22Refined85.d3224 (change p 249 (some 248)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 249 (some 248) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter1000 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 252 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 252))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at252]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 252)))]
  change NetHack.Sokoban22Refined85.d3224 p = _
  exact oldNode3224 p
theorem oldAfter1001 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 252 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 252 (.fill 253)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at252]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 252 (.fill 253))))]
  have hazardsIgnored : Agree NetHack.Sokoban22Refined85.support (HazardPattern.afterPattern 10000 p (.push 252 (.fill 253))) (change p 252 none) := by
    intro c member
    have bound := prior_bounded c member
    have ne : 10000 + 253 ≠ c := by simp only [Cell] at *; omega
    simp [HazardPattern.afterPattern, change, ne]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ hazardsIgnored]
  have representative := change_representative NetHack.Sokoban22Refined85.support p 252 none 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter1002 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 252 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 252 (.stay 253)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at252]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 252 (.stay 253))))]
  change NetHack.Sokoban22Refined85.d3224 (change p 252 (some 253)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 252 (some 253) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter1003 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 250 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 250))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at250]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 250)))]
  change NetHack.Sokoban22Refined85.d3224 p = _
  exact oldNode3224 p
theorem oldAfter1004 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 250 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 250 (.stay 245)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at250]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 250 (.stay 245))))]
  change NetHack.Sokoban22Refined85.d3224 (change p 250 (some 245)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 250 (some 245) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter1005 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 253 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 253))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at253]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 253)))]
  change NetHack.Sokoban22Refined85.d3224 p = _
  exact oldNode3224 p
theorem oldAfter1006 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 253 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 253 (.fill 254)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at253]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 253 (.fill 254))))]
  have hazardsIgnored : Agree NetHack.Sokoban22Refined85.support (HazardPattern.afterPattern 10000 p (.push 253 (.fill 254))) (change p 253 none) := by
    intro c member
    have bound := prior_bounded c member
    have ne : 10000 + 254 ≠ c := by simp only [Cell] at *; omega
    simp [HazardPattern.afterPattern, change, ne]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ hazardsIgnored]
  have representative := change_representative NetHack.Sokoban22Refined85.support p 253 none 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter1007 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 253 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 253 (.stay 254)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at253]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 253 (.stay 254))))]
  change NetHack.Sokoban22Refined85.d3224 (change p 253 (some 254)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 253 (some 254) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter1008 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 251 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 251))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at251]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 251)))]
  change NetHack.Sokoban22Refined85.d3224 p = _
  exact oldNode3224 p
theorem oldAfter1009 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 251 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 251 (.fill 250)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at251]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 251 (.fill 250))))]
  have hazardsIgnored : Agree NetHack.Sokoban22Refined85.support (HazardPattern.afterPattern 10000 p (.push 251 (.fill 250))) (change p 251 none) := by
    intro c member
    have bound := prior_bounded c member
    have ne : 10000 + 250 ≠ c := by simp only [Cell] at *; omega
    simp [HazardPattern.afterPattern, change, ne]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ hazardsIgnored]
  have representative := change_representative NetHack.Sokoban22Refined85.support p 251 none 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter1010 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 251 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 251 (.stay 250)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at251]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 251 (.stay 250))))]
  change NetHack.Sokoban22Refined85.d3224 (change p 251 (some 250)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 251 (some 250) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter1011 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 254 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 254))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at254]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 254)))]
  change NetHack.Sokoban22Refined85.d3224 p = _
  exact oldNode3224 p
theorem oldAfter1012 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 254 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 254 (.fill 255)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at254]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 254 (.fill 255))))]
  have hazardsIgnored : Agree NetHack.Sokoban22Refined85.support (HazardPattern.afterPattern 10000 p (.push 254 (.fill 255))) (change p 254 none) := by
    intro c member
    have bound := prior_bounded c member
    have ne : 10000 + 255 ≠ c := by simp only [Cell] at *; omega
    simp [HazardPattern.afterPattern, change, ne]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ hazardsIgnored]
  have representative := change_representative NetHack.Sokoban22Refined85.support p 254 none 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter1013 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 254 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 254 (.stay 255)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at254]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 254 (.stay 255))))]
  change NetHack.Sokoban22Refined85.d3224 (change p 254 (some 255)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 254 (some 255) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter1014 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 252 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 252))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at252]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 252)))]
  change NetHack.Sokoban22Refined85.d3224 p = _
  exact oldNode3224 p
theorem oldAfter1015 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 252 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 252 (.fill 251)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at252]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 252 (.fill 251))))]
  have hazardsIgnored : Agree NetHack.Sokoban22Refined85.support (HazardPattern.afterPattern 10000 p (.push 252 (.fill 251))) (change p 252 none) := by
    intro c member
    have bound := prior_bounded c member
    have ne : 10000 + 251 ≠ c := by simp only [Cell] at *; omega
    simp [HazardPattern.afterPattern, change, ne]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ hazardsIgnored]
  have representative := change_representative NetHack.Sokoban22Refined85.support p 252 none 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter1016 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 252 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 252 (.stay 251)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at252]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 252 (.stay 251))))]
  change NetHack.Sokoban22Refined85.d3224 (change p 252 (some 251)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 252 (some 251) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter1017 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 255 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 255))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at255]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 255)))]
  change NetHack.Sokoban22Refined85.d3224 p = _
  exact oldNode3224 p
theorem oldAfter1018 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 255 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 255 (.fill 256)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at255]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 255 (.fill 256))))]
  have hazardsIgnored : Agree NetHack.Sokoban22Refined85.support (HazardPattern.afterPattern 10000 p (.push 255 (.fill 256))) (change p 255 none) := by
    intro c member
    have bound := prior_bounded c member
    have ne : 10000 + 256 ≠ c := by simp only [Cell] at *; omega
    simp [HazardPattern.afterPattern, change, ne]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ hazardsIgnored]
  have representative := change_representative NetHack.Sokoban22Refined85.support p 255 none 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter1019 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 255 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 255 (.stay 256)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at255]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 255 (.stay 256))))]
  change NetHack.Sokoban22Refined85.d3224 (change p 255 (some 256)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 255 (some 256) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter1020 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 253 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 253))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at253]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 253)))]
  change NetHack.Sokoban22Refined85.d3224 p = _
  exact oldNode3224 p
theorem oldAfter1021 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 253 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 253 (.fill 252)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at253]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 253 (.fill 252))))]
  have hazardsIgnored : Agree NetHack.Sokoban22Refined85.support (HazardPattern.afterPattern 10000 p (.push 253 (.fill 252))) (change p 253 none) := by
    intro c member
    have bound := prior_bounded c member
    have ne : 10000 + 252 ≠ c := by simp only [Cell] at *; omega
    simp [HazardPattern.afterPattern, change, ne]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ hazardsIgnored]
  have representative := change_representative NetHack.Sokoban22Refined85.support p 253 none 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter1022 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 253 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 253 (.stay 252)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at253]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 253 (.stay 252))))]
  change NetHack.Sokoban22Refined85.d3224 (change p 253 (some 252)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 253 (some 252) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter1023 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 256 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 256))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at256]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 256)))]
  change NetHack.Sokoban22Refined85.d3224 p = _
  exact oldNode3224 p
theorem oldAfter1024 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 256 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 256 (.fill 257)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at256]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 256 (.fill 257))))]
  have hazardsIgnored : Agree NetHack.Sokoban22Refined85.support (HazardPattern.afterPattern 10000 p (.push 256 (.fill 257))) (change p 256 none) := by
    intro c member
    have bound := prior_bounded c member
    have ne : 10000 + 257 ≠ c := by simp only [Cell] at *; omega
    simp [HazardPattern.afterPattern, change, ne]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ hazardsIgnored]
  have representative := change_representative NetHack.Sokoban22Refined85.support p 256 none 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter1025 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 256 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 256 (.stay 257)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at256]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 256 (.stay 257))))]
  change NetHack.Sokoban22Refined85.d3224 (change p 256 (some 257)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 256 (some 257) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter1026 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 254 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 254))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at254]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 254)))]
  change NetHack.Sokoban22Refined85.d3224 p = _
  exact oldNode3224 p
theorem oldAfter1027 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 254 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 254 (.fill 253)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at254]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 254 (.fill 253))))]
  have hazardsIgnored : Agree NetHack.Sokoban22Refined85.support (HazardPattern.afterPattern 10000 p (.push 254 (.fill 253))) (change p 254 none) := by
    intro c member
    have bound := prior_bounded c member
    have ne : 10000 + 253 ≠ c := by simp only [Cell] at *; omega
    simp [HazardPattern.afterPattern, change, ne]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ hazardsIgnored]
  have representative := change_representative NetHack.Sokoban22Refined85.support p 254 none 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter1028 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 254 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 254 (.stay 253)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at254]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 254 (.stay 253))))]
  change NetHack.Sokoban22Refined85.d3224 (change p 254 (some 253)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 254 (some 253) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter1029 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 257 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 257))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at257]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 257)))]
  change NetHack.Sokoban22Refined85.d3224 p = _
  exact oldNode3224 p
theorem oldAfter1030 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 257 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 257 (.fill 258)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at257]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 257 (.fill 258))))]
  have hazardsIgnored : Agree NetHack.Sokoban22Refined85.support (HazardPattern.afterPattern 10000 p (.push 257 (.fill 258))) (change p 257 none) := by
    intro c member
    have bound := prior_bounded c member
    have ne : 10000 + 258 ≠ c := by simp only [Cell] at *; omega
    simp [HazardPattern.afterPattern, change, ne]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ hazardsIgnored]
  have representative := change_representative NetHack.Sokoban22Refined85.support p 257 none 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter1031 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 257 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 257 (.stay 258)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at257]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 257 (.stay 258))))]
  change NetHack.Sokoban22Refined85.d3224 (change p 257 (some 258)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 257 (some 258) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter1032 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 255 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 255))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at255]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 255)))]
  change NetHack.Sokoban22Refined85.d3224 p = _
  exact oldNode3224 p
theorem oldAfter1033 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 255 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 255 (.fill 254)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at255]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 255 (.fill 254))))]
  have hazardsIgnored : Agree NetHack.Sokoban22Refined85.support (HazardPattern.afterPattern 10000 p (.push 255 (.fill 254))) (change p 255 none) := by
    intro c member
    have bound := prior_bounded c member
    have ne : 10000 + 254 ≠ c := by simp only [Cell] at *; omega
    simp [HazardPattern.afterPattern, change, ne]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ hazardsIgnored]
  have representative := change_representative NetHack.Sokoban22Refined85.support p 255 none 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter1034 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 255 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 255 (.stay 254)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at255]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 255 (.stay 254))))]
  change NetHack.Sokoban22Refined85.d3224 (change p 255 (some 254)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 255 (some 254) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter1035 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 258 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 258))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at258]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 258)))]
  change NetHack.Sokoban22Refined85.d3224 p = _
  exact oldNode3224 p
theorem oldAfter1036 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 258 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 258 (.fill 259)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at258]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 258 (.fill 259))))]
  have hazardsIgnored : Agree NetHack.Sokoban22Refined85.support (HazardPattern.afterPattern 10000 p (.push 258 (.fill 259))) (change p 258 none) := by
    intro c member
    have bound := prior_bounded c member
    have ne : 10000 + 259 ≠ c := by simp only [Cell] at *; omega
    simp [HazardPattern.afterPattern, change, ne]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ hazardsIgnored]
  have representative := change_representative NetHack.Sokoban22Refined85.support p 258 none 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter1037 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 258 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 258 (.stay 259)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at258]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 258 (.stay 259))))]
  change NetHack.Sokoban22Refined85.d3224 (change p 258 (some 259)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 258 (some 259) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
theorem oldAfter1038 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 256 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 256))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at256]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 256)))]
  change NetHack.Sokoban22Refined85.d3224 p = _
  exact oldNode3224 p
theorem oldAfter1039 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 256 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 256 (.fill 255)))) = d50823 p := by
  rw [NetHack.Sokoban22Refined85.at256]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 256 (.fill 255))))]
  have hazardsIgnored : Agree NetHack.Sokoban22Refined85.support (HazardPattern.afterPattern 10000 p (.push 256 (.fill 255))) (change p 256 none) := by
    intro c member
    have bound := prior_bounded c member
    have ne : 10000 + 255 ≠ c := by simp only [Cell] at *; omega
    simp [HazardPattern.afterPattern, change, ne]
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ hazardsIgnored]
  have representative := change_representative NetHack.Sokoban22Refined85.support p 256 none 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree3224 _ _ representative]
  change NetHack.Sokoban22Refined85.d3224 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub9234]
  exact oldNode3224 p
end NetHack.Soko22Hazard87
