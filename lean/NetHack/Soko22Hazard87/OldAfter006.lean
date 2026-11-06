import NetHack.Soko22Hazard87.OldAfter005
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
namespace Prior
end Prior
theorem oldAfter480 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 135 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 135))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at135]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 135)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter481 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 135 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 135 (.stay 134)))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at135]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 135 (.stay 134))))]
  change NetHack.Sokoban22Refined85.d267 (change p 135 (some 134)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 135 (some 134) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree267 _ _ representative]
  change NetHack.Sokoban22Refined85.d267 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub267]
  exact oldNode267 p
theorem oldAfter482 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 115 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 115))) = d48097 p := by
  rw [NetHack.Sokoban22Refined85.at115]
  rw [NetHack.Sokoban22Refined85.agree498 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 115)))]
  change NetHack.Sokoban22Refined85.d498 p = _
  exact oldNode498 p
theorem oldAfter483 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 113 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 113))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at113]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 113)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter484 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 159 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 159))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at159]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 159)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter485 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 157 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 157))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at157]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 157)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter486 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 116 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 116))) = d48115 p := by
  rw [NetHack.Sokoban22Refined85.at116]
  rw [NetHack.Sokoban22Refined85.agree516 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 116)))]
  change NetHack.Sokoban22Refined85.d516 p = _
  exact oldNode516 p
theorem oldAfter487 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 116 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 116 (.stay 94)))) = d126872 p := by
  rw [NetHack.Sokoban22Refined85.at116]
  rw [NetHack.Sokoban22Refined85.agree516 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 116 (.stay 94))))]
  change NetHack.Sokoban22Refined85.d516 (change p 116 (some 94)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 116 (some 94) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree516 _ _ representative]
  change NetHack.Sokoban22Refined85.d516 (change p 116 none) = _
  rw [NetHack.Sokoban22Refined85.sub3496]
  exact oldNode4202 p
theorem oldAfter488 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 160 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 160))) = d48388 p := by
  rw [NetHack.Sokoban22Refined85.at160]
  rw [NetHack.Sokoban22Refined85.agree789 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 160)))]
  change NetHack.Sokoban22Refined85.d789 p = _
  exact oldNode789 p
theorem oldAfter489 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 160 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 160 (.stay 182)))) = d128576 p := by
  rw [NetHack.Sokoban22Refined85.at160]
  rw [NetHack.Sokoban22Refined85.agree789 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 160 (.stay 182))))]
  change NetHack.Sokoban22Refined85.d789 (change p 160 (some 182)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 160 (some 182) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree789 _ _ representative]
  change NetHack.Sokoban22Refined85.d789 (change p 160 (some 182)) = _
  rw [NetHack.Sokoban22Refined85.sub3690]
  exact oldNode4297 p
theorem oldAfter490 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 115 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 115))) = d48097 p := by
  rw [NetHack.Sokoban22Refined85.at115]
  rw [NetHack.Sokoban22Refined85.agree498 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 115)))]
  change NetHack.Sokoban22Refined85.d498 p = _
  exact oldNode498 p
theorem oldAfter491 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 161 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 161))) = d48547 p := by
  rw [NetHack.Sokoban22Refined85.at161]
  rw [NetHack.Sokoban22Refined85.agree948 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 161)))]
  change NetHack.Sokoban22Refined85.d948 p = _
  exact oldNode948 p
theorem oldAfter492 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 159 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 159))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at159]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 159)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter493 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 119 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 119))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at119]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 119)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter494 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 119 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 119 (.stay 97)))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at119]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 119 (.stay 97))))]
  change NetHack.Sokoban22Refined85.d312 (change p 119 (some 97)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 119 (some 97) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree312 _ _ representative]
  change NetHack.Sokoban22Refined85.d312 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub412]
  exact oldNode312 p
theorem oldAfter495 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 163 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 163))) = d48997 p := by
  rw [NetHack.Sokoban22Refined85.at163]
  rw [NetHack.Sokoban22Refined85.agree1398 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 163)))]
  change NetHack.Sokoban22Refined85.d1398 p = _
  exact oldNode1398 p
theorem oldAfter496 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 163 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 163 (.stay 185)))) = d130479 p := by
  rw [NetHack.Sokoban22Refined85.at163]
  rw [NetHack.Sokoban22Refined85.agree1398 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 163 (.stay 185))))]
  change NetHack.Sokoban22Refined85.d1398 (change p 163 (some 185)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 163 (some 185) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree1398 _ _ representative]
  change NetHack.Sokoban22Refined85.d1398 (change p 163 none) = _
  rw [NetHack.Sokoban22Refined85.sub4017]
  exact oldNode4393 p
theorem oldAfter497 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 120 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 120))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at120]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 120)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter498 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 118 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 118))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at118]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 118)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter499 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 164 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 164))) = d49102 p := by
  rw [NetHack.Sokoban22Refined85.at164]
  rw [NetHack.Sokoban22Refined85.agree1503 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 164)))]
  change NetHack.Sokoban22Refined85.d1503 p = _
  exact oldNode1503 p
theorem oldAfter500 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 162 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 162))) = d48749 p := by
  rw [NetHack.Sokoban22Refined85.at162]
  rw [NetHack.Sokoban22Refined85.agree1150 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 162)))]
  change NetHack.Sokoban22Refined85.d1150 p = _
  exact oldNode1150 p
theorem oldAfter501 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 122 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 122))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at122]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 122)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter502 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 122 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 122 (.stay 100)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at122]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 122 (.stay 100))))]
  change NetHack.Sokoban22Refined85.d0 (change p 122 (some 100)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 122 (some 100) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter503 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 166 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 166))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at166]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 166)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter504 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 166 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 166 (.stay 188)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at166]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 166 (.stay 188))))]
  change NetHack.Sokoban22Refined85.d0 (change p 166 (some 188)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 166 (some 188) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter505 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 145 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 145))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at145]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 145)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter506 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 145 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 145 (.stay 146)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at145]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 145 (.stay 146))))]
  change NetHack.Sokoban22Refined85.d0 (change p 145 (some 146)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 145 (some 146) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter507 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 123 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 123))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at123]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 123)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter508 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 167 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 167))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at167]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 167)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter509 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 123 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 123))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at123]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 123)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter510 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 123 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 123 (.stay 101)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at123]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 123 (.stay 101))))]
  change NetHack.Sokoban22Refined85.d0 (change p 123 (some 101)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 123 (some 101) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter511 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 167 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 167))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at167]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 167)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter512 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 167 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 167 (.stay 189)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at167]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 167 (.stay 189))))]
  change NetHack.Sokoban22Refined85.d0 (change p 167 (some 189)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 167 (some 189) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter513 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 146 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 146))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at146]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 146)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter514 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 146 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 146 (.stay 147)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at146]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 146 (.stay 147))))]
  change NetHack.Sokoban22Refined85.d0 (change p 146 (some 147)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 146 (some 147) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter515 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 144 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 144))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at144]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 144)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter516 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 124 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 124))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at124]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 124)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter517 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 122 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 122))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at122]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 122)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter518 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 168 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 168))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at168]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 168)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter519 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 166 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 166))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at166]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 166)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter520 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 124 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 124))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at124]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 124)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter521 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 124 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 124 (.stay 102)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at124]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 124 (.stay 102))))]
  change NetHack.Sokoban22Refined85.d0 (change p 124 (some 102)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 124 (some 102) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter522 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 168 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 168))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at168]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 168)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter523 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 168 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 168 (.stay 190)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at168]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 168 (.stay 190))))]
  change NetHack.Sokoban22Refined85.d0 (change p 168 (some 190)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 168 (some 190) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter524 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 147 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 147))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at147]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 147)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter525 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 147 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 147 (.stay 148)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at147]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 147 (.stay 148))))]
  change NetHack.Sokoban22Refined85.d0 (change p 147 (some 148)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 147 (some 148) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter526 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 145 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 145))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at145]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 145)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter527 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 145 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 145 (.stay 144)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at145]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 145 (.stay 144))))]
  change NetHack.Sokoban22Refined85.d0 (change p 145 (some 144)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 145 (some 144) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter528 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 125 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 125))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at125]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 125)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter529 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 123 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 123))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at123]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 123)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter530 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 169 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 169))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at169]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 169)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter531 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 167 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 167))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at167]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 167)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter532 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 125 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 125))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at125]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 125)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter533 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 125 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 125 (.stay 103)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at125]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 125 (.stay 103))))]
  change NetHack.Sokoban22Refined85.d0 (change p 125 (some 103)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 125 (some 103) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter534 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 169 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 169))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at169]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 169)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter535 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 169 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 169 (.stay 191)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at169]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 169 (.stay 191))))]
  change NetHack.Sokoban22Refined85.d0 (change p 169 (some 191)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 169 (some 191) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter536 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 148 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 148))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at148]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 148)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter537 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 148 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 148 (.stay 149)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at148]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 148 (.stay 149))))]
  change NetHack.Sokoban22Refined85.d0 (change p 148 (some 149)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 148 (some 149) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter538 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 146 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 146))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at146]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 146)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter539 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 146 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 146 (.stay 145)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at146]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 146 (.stay 145))))]
  change NetHack.Sokoban22Refined85.d0 (change p 146 (some 145)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 146 (some 145) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter540 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 126 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 126))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at126]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 126)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter541 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 124 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 124))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at124]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 124)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter542 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 170 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 170))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at170]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 170)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter543 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 168 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 168))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at168]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 168)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter544 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 126 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 126))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at126]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 126)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter545 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 126 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 126 (.stay 104)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at126]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 126 (.stay 104))))]
  change NetHack.Sokoban22Refined85.d0 (change p 126 (some 104)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 126 (some 104) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter546 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 170 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 170))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at170]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 170)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter547 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 170 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 170 (.stay 192)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at170]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 170 (.stay 192))))]
  change NetHack.Sokoban22Refined85.d0 (change p 170 (some 192)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 170 (some 192) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter548 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 149 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 149))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at149]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 149)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter549 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 149 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 149 (.stay 150)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at149]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 149 (.stay 150))))]
  change NetHack.Sokoban22Refined85.d0 (change p 149 (some 150)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 149 (some 150) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter550 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 147 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 147))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at147]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 147)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter551 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 147 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 147 (.stay 146)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at147]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 147 (.stay 146))))]
  change NetHack.Sokoban22Refined85.d0 (change p 147 (some 146)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 147 (some 146) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter552 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 127 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 127))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at127]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 127)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter553 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 125 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 125))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at125]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 125)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter554 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 171 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 171))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at171]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 171)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter555 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 169 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 169))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at169]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 169)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter556 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 127 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 127))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at127]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 127)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter557 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 127 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 127 (.stay 105)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at127]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 127 (.stay 105))))]
  change NetHack.Sokoban22Refined85.d0 (change p 127 (some 105)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 127 (some 105) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter558 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 171 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 171))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at171]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 171)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter559 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 171 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 171 (.stay 193)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at171]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 171 (.stay 193))))]
  change NetHack.Sokoban22Refined85.d0 (change p 171 (some 193)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 171 (some 193) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
end NetHack.Soko22Hazard87
