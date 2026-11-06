import NetHack.Soko22Hazard87.OldAfter004
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
namespace Prior
end Prior
theorem oldAfter400 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 146 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 146))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at146]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 146)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter401 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 146 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 146 (.stay 168)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at146]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 146 (.stay 168))))]
  change NetHack.Sokoban22Refined85.d0 (change p 146 (some 168)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 146 (some 168) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter402 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 125 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 125))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at125]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 125)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter403 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 125 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 125 (.stay 126)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at125]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 125 (.stay 126))))]
  change NetHack.Sokoban22Refined85.d0 (change p 125 (some 126)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 125 (some 126) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter404 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 123 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 123))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at123]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 123)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter405 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 123 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 123 (.stay 122)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at123]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 123 (.stay 122))))]
  change NetHack.Sokoban22Refined85.d0 (change p 123 (some 122)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 123 (some 122) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter406 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 103 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 103))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at103]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 103)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter407 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 101 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 101))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at101]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 101)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter408 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 147 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 147))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at147]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 147)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter409 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 145 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 145))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at145]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 145)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter410 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 103 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 103))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at103]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 103)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter411 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 103 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 103 (.stay 81)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at103]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 103 (.stay 81))))]
  change NetHack.Sokoban22Refined85.d0 (change p 103 (some 81)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 103 (some 81) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter412 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 147 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 147))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at147]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 147)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter413 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 147 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 147 (.stay 169)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at147]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 147 (.stay 169))))]
  change NetHack.Sokoban22Refined85.d0 (change p 147 (some 169)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 147 (some 169) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter414 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 126 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 126))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at126]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 126)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter415 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 126 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 126 (.stay 127)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at126]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 126 (.stay 127))))]
  change NetHack.Sokoban22Refined85.d0 (change p 126 (some 127)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 126 (some 127) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter416 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 124 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 124))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at124]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 124)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter417 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 124 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 124 (.stay 123)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at124]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 124 (.stay 123))))]
  change NetHack.Sokoban22Refined85.d0 (change p 124 (some 123)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 124 (some 123) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter418 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 104 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 104))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at104]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 104)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter419 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 102 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 102))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at102]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 102)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter420 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 148 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 148))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at148]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 148)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter421 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 146 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 146))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at146]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 146)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter422 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 104 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 104))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at104]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 104)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter423 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 104 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 104 (.stay 82)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at104]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 104 (.stay 82))))]
  change NetHack.Sokoban22Refined85.d0 (change p 104 (some 82)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 104 (some 82) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter424 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 148 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 148))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at148]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 148)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter425 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 148 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 148 (.stay 170)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at148]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 148 (.stay 170))))]
  change NetHack.Sokoban22Refined85.d0 (change p 148 (some 170)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 148 (some 170) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter426 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 127 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 127))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at127]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 127)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter427 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 127 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 127 (.stay 128)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at127]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 127 (.stay 128))))]
  change NetHack.Sokoban22Refined85.d0 (change p 127 (some 128)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 127 (some 128) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter428 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 125 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 125))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at125]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 125)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter429 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 125 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 125 (.stay 124)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at125]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 125 (.stay 124))))]
  change NetHack.Sokoban22Refined85.d0 (change p 125 (some 124)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 125 (some 124) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter430 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 105 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 105))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at105]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 105)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter431 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 103 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 103))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at103]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 103)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter432 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 149 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 149))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at149]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 149)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter433 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 147 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 147))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at147]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 147)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter434 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 105 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 105))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at105]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 105)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter435 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 105 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 105 (.stay 83)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at105]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 105 (.stay 83))))]
  change NetHack.Sokoban22Refined85.d0 (change p 105 (some 83)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 105 (some 83) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter436 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 149 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 149))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at149]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 149)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter437 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 149 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 149 (.stay 171)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at149]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 149 (.stay 171))))]
  change NetHack.Sokoban22Refined85.d0 (change p 149 (some 171)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 149 (some 171) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter438 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 128 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 128))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at128]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 128)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter439 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 126 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 126))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at126]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 126)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter440 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 126 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 126 (.stay 125)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at126]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 126 (.stay 125))))]
  change NetHack.Sokoban22Refined85.d0 (change p 126 (some 125)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 126 (some 125) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter441 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 106 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 106))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at106]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 106)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter442 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 104 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 104))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at104]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 104)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter443 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 150 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 150))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at150]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 150)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter444 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 148 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 148))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at148]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 148)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter445 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 106 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 106))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at106]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 106)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter446 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 106 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 106 (.stay 84)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at106]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 106 (.stay 84))))]
  change NetHack.Sokoban22Refined85.d0 (change p 106 (some 84)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 106 (some 84) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter447 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 150 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 150))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at150]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 150)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter448 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 150 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 150 (.stay 172)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at150]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 150 (.stay 172))))]
  change NetHack.Sokoban22Refined85.d0 (change p 150 (some 172)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 150 (some 172) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter449 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 127 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 127))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at127]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 127)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter450 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 127 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 127 (.stay 126)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at127]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 127 (.stay 126))))]
  change NetHack.Sokoban22Refined85.d0 (change p 127 (some 126)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 127 (some 126) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter451 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 105 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 105))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at105]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 105)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter452 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 149 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 149))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at149]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 149)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter453 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 111 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 111))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at111]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 111)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter454 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 111 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 111 (.stay 89)))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at111]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 111 (.stay 89))))]
  change NetHack.Sokoban22Refined85.d267 (change p 111 (some 89)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 111 (some 89) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree267 _ _ representative]
  change NetHack.Sokoban22Refined85.d267 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub267]
  exact oldNode267 p
theorem oldAfter455 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 155 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 155))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at155]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 155)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter456 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 155 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 155 (.stay 177)))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at155]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 155 (.stay 177))))]
  change NetHack.Sokoban22Refined85.d267 (change p 155 (some 177)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 155 (some 177) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree267 _ _ representative]
  change NetHack.Sokoban22Refined85.d267 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub267]
  exact oldNode267 p
theorem oldAfter457 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 134 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 134))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at134]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 134)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter458 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 134 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 134 (.stay 135)))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at134]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 134 (.stay 135))))]
  change NetHack.Sokoban22Refined85.d267 (change p 134 (some 135)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 134 (some 135) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree267 _ _ representative]
  change NetHack.Sokoban22Refined85.d267 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub267]
  exact oldNode267 p
theorem oldAfter459 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 156 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 156))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at156]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 156)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter460 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 156 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 156))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at156]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 156)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter461 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 135 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 135))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at135]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 135)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter462 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 135 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 135 (.stay 136)))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at135]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 135 (.stay 136))))]
  change NetHack.Sokoban22Refined85.d267 (change p 135 (some 136)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 135 (some 136) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree267 _ _ representative]
  change NetHack.Sokoban22Refined85.d267 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub267]
  exact oldNode267 p
theorem oldAfter463 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 133 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 133))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at133]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 133)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter464 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 113 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 113))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at113]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 113)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter465 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 111 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 111))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at111]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 111)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter466 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 157 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 157))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at157]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 157)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter467 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 155 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 155))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at155]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 155)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter468 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 113 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 113))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at113]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 113)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter469 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 113 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 113 (.stay 91)))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at113]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 113 (.stay 91))))]
  change NetHack.Sokoban22Refined85.d267 (change p 113 (some 91)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 113 (some 91) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree267 _ _ representative]
  change NetHack.Sokoban22Refined85.d267 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub267]
  exact oldNode267 p
theorem oldAfter470 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 157 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 157))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at157]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 157)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter471 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 136 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 136))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at136]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 136)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter472 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 134 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 134))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at134]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 134)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter473 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 134 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 134 (.stay 133)))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at134]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 134 (.stay 133))))]
  change NetHack.Sokoban22Refined85.d267 (change p 134 (some 133)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 134 (some 133) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree267 _ _ representative]
  change NetHack.Sokoban22Refined85.d267 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub267]
  exact oldNode267 p
theorem oldAfter474 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 114 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 114))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at114]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 114)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter475 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 158 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 158))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at158]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 158)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter476 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 156 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 156))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at156]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 156)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter477 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 114 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 114))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at114]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 114)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter478 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 158 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 158))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at158]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 158)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter479 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 158 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 158 (.stay 180)))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at158]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 158 (.stay 180))))]
  change NetHack.Sokoban22Refined85.d267 (change p 158 (some 180)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 158 (some 180) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree267 _ _ representative]
  change NetHack.Sokoban22Refined85.d267 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub267]
  exact oldNode267 p
end NetHack.Soko22Hazard87
