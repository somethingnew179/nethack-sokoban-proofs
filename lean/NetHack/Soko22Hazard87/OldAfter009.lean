import NetHack.Soko22Hazard87.OldAfter008
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
namespace Prior
end Prior
theorem oldAfter720 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 150 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 150 (.stay 128)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at150]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 150 (.stay 128))))]
  change NetHack.Sokoban22Refined85.d0 (change p 150 (some 128)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 150 (some 128) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter721 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 194 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 194))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at194]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 194)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter722 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 194 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 194 (.stay 216)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at194]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 194 (.stay 216))))]
  change NetHack.Sokoban22Refined85.d0 (change p 194 (some 216)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 194 (some 216) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter723 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 171 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 171))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at171]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 171)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter724 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 171 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 171 (.stay 170)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at171]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 171 (.stay 170))))]
  change NetHack.Sokoban22Refined85.d0 (change p 171 (some 170)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 171 (some 170) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter725 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 149 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 149))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at149]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 149)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter726 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 193 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 193))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at193]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 193)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter727 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 155 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 155))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at155]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 155)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter728 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 155 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 155 (.stay 133)))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at155]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 155 (.stay 133))))]
  change NetHack.Sokoban22Refined85.d267 (change p 155 (some 133)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 155 (some 133) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree267 _ _ representative]
  change NetHack.Sokoban22Refined85.d267 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub267]
  exact oldNode267 p
theorem oldAfter729 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 199 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 199))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at199]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 199)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter730 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 156 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 156))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at156]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 156)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter731 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 200 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 200))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at200]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 200)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter732 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 158 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 158))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at158]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 158)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter733 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 158 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 158 (.stay 136)))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at158]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 158 (.stay 136))))]
  change NetHack.Sokoban22Refined85.d267 (change p 158 (some 136)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 158 (some 136) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree267 _ _ representative]
  change NetHack.Sokoban22Refined85.d267 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub267]
  exact oldNode267 p
theorem oldAfter734 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 202 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 202))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at202]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 202)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter735 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 202 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 202 (.stay 224)))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at202]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 202 (.stay 224))))]
  change NetHack.Sokoban22Refined85.d267 (change p 202 (some 224)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 202 (some 224) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree267 _ _ representative]
  change NetHack.Sokoban22Refined85.d267 (change p 10000 (some 224)) = _
  rw [NetHack.Sokoban22Refined85.sub6825]
  exact oldNode267 p
theorem oldAfter736 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 181 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 181))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at181]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 181)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter737 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 181 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 181 (.stay 182)))) = d208030 p := by
  rw [NetHack.Sokoban22Refined85.at181]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 181 (.stay 182))))]
  change NetHack.Sokoban22Refined85.d267 (change p 181 (some 182)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 181 (some 182) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree267 _ _ representative]
  change NetHack.Sokoban22Refined85.d267 (change p 10000 (some 182)) = _
  rw [NetHack.Sokoban22Refined85.sub7093]
  exact oldNode4966 p
theorem oldAfter738 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 159 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 159))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at159]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 159)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter739 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 157 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 157))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at157]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 157)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter740 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 201 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 201))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at201]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 201)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter741 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 159 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 159))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at159]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 159)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter742 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 182 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 182))) = d49280 p := by
  rw [NetHack.Sokoban22Refined85.at182]
  rw [NetHack.Sokoban22Refined85.agree1681 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 182)))]
  change NetHack.Sokoban22Refined85.d1681 p = _
  exact oldNode1681 p
theorem oldAfter743 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 180 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 180))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at180]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 180)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter744 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 160 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 160))) = d48388 p := by
  rw [NetHack.Sokoban22Refined85.at160]
  rw [NetHack.Sokoban22Refined85.agree789 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 160)))]
  change NetHack.Sokoban22Refined85.d789 p = _
  exact oldNode789 p
theorem oldAfter745 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 158 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 158))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at158]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 158)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter746 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 204 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 204))) = d49782 p := by
  rw [NetHack.Sokoban22Refined85.at204]
  rw [NetHack.Sokoban22Refined85.agree2183 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 204)))]
  change NetHack.Sokoban22Refined85.d2183 p = _
  exact oldNode2183 p
theorem oldAfter747 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 202 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 202))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at202]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 202)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter748 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 160 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 160))) = d48388 p := by
  rw [NetHack.Sokoban22Refined85.at160]
  rw [NetHack.Sokoban22Refined85.agree789 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 160)))]
  change NetHack.Sokoban22Refined85.d789 p = _
  exact oldNode789 p
theorem oldAfter749 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 160 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 160 (.stay 138)))) = d212576 p := by
  rw [NetHack.Sokoban22Refined85.at160]
  rw [NetHack.Sokoban22Refined85.agree789 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 160 (.stay 138))))]
  change NetHack.Sokoban22Refined85.d789 (change p 160 (some 138)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 160 (some 138) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree789 _ _ representative]
  change NetHack.Sokoban22Refined85.d789 (change p 160 (some 138)) = _
  rw [NetHack.Sokoban22Refined85.sub7258]
  exact oldNode4984 p
theorem oldAfter750 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 204 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 204))) = d49782 p := by
  rw [NetHack.Sokoban22Refined85.at204]
  rw [NetHack.Sokoban22Refined85.agree2183 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 204)))]
  change NetHack.Sokoban22Refined85.d2183 p = _
  exact oldNode2183 p
theorem oldAfter751 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 204 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 204 (.stay 226)))) = d216729 p := by
  rw [NetHack.Sokoban22Refined85.at204]
  rw [NetHack.Sokoban22Refined85.agree2183 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 204 (.stay 226))))]
  change NetHack.Sokoban22Refined85.d2183 (change p 204 (some 226)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 204 (some 226) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree2183 _ _ representative]
  change NetHack.Sokoban22Refined85.d2183 (change p 204 none) = _
  rw [NetHack.Sokoban22Refined85.sub7823]
  exact oldNode5243 p
theorem oldAfter752 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 181 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 181))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at181]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 181)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter753 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 181 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 181 (.stay 180)))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at181]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 181 (.stay 180))))]
  change NetHack.Sokoban22Refined85.d267 (change p 181 (some 180)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 181 (some 180) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree267 _ _ representative]
  change NetHack.Sokoban22Refined85.d267 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub267]
  exact oldNode267 p
theorem oldAfter754 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 161 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 161))) = d48547 p := by
  rw [NetHack.Sokoban22Refined85.at161]
  rw [NetHack.Sokoban22Refined85.agree948 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 161)))]
  change NetHack.Sokoban22Refined85.d948 p = _
  exact oldNode948 p
theorem oldAfter755 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 159 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 159))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at159]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 159)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter756 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 162 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 162))) = d48749 p := by
  rw [NetHack.Sokoban22Refined85.at162]
  rw [NetHack.Sokoban22Refined85.agree1150 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 162)))]
  change NetHack.Sokoban22Refined85.d1150 p = _
  exact oldNode1150 p
theorem oldAfter757 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 185 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 185))) = d49102 p := by
  rw [NetHack.Sokoban22Refined85.at185]
  rw [NetHack.Sokoban22Refined85.agree1503 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 185)))]
  change NetHack.Sokoban22Refined85.d1503 p = _
  exact oldNode1503 p
theorem oldAfter758 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 185 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 185 (.stay 186)))) = d49102 p := by
  rw [NetHack.Sokoban22Refined85.at185]
  rw [NetHack.Sokoban22Refined85.agree1503 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 185 (.stay 186))))]
  change NetHack.Sokoban22Refined85.d1503 (change p 185 (some 186)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 185 (some 186) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree1503 _ _ representative]
  change NetHack.Sokoban22Refined85.d1503 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub7977]
  exact oldNode1503 p
theorem oldAfter759 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 163 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 163))) = d48997 p := by
  rw [NetHack.Sokoban22Refined85.at163]
  rw [NetHack.Sokoban22Refined85.agree1398 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 163)))]
  change NetHack.Sokoban22Refined85.d1398 p = _
  exact oldNode1398 p
theorem oldAfter760 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 161 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 161))) = d48547 p := by
  rw [NetHack.Sokoban22Refined85.at161]
  rw [NetHack.Sokoban22Refined85.agree948 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 161)))]
  change NetHack.Sokoban22Refined85.d948 p = _
  exact oldNode948 p
theorem oldAfter761 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 163 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 163))) = d48997 p := by
  rw [NetHack.Sokoban22Refined85.at163]
  rw [NetHack.Sokoban22Refined85.agree1398 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 163)))]
  change NetHack.Sokoban22Refined85.d1398 p = _
  exact oldNode1398 p
theorem oldAfter762 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 163 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 163 (.stay 141)))) = d225614 p := by
  rw [NetHack.Sokoban22Refined85.at163]
  rw [NetHack.Sokoban22Refined85.agree1398 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 163 (.stay 141))))]
  change NetHack.Sokoban22Refined85.d1398 (change p 163 (some 141)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 163 (some 141) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree1398 _ _ representative]
  change NetHack.Sokoban22Refined85.d1398 (change p 163 (some 141)) = _
  rw [NetHack.Sokoban22Refined85.sub8183]
  exact oldNode5266 p
theorem oldAfter763 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 186 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 186))) = d49102 p := by
  rw [NetHack.Sokoban22Refined85.at186]
  rw [NetHack.Sokoban22Refined85.agree1503 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 186)))]
  change NetHack.Sokoban22Refined85.d1503 p = _
  exact oldNode1503 p
theorem oldAfter764 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 184 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 184))) = d49102 p := by
  rw [NetHack.Sokoban22Refined85.at184]
  rw [NetHack.Sokoban22Refined85.agree1503 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 184)))]
  change NetHack.Sokoban22Refined85.d1503 p = _
  exact oldNode1503 p
theorem oldAfter765 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 164 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 164))) = d49102 p := by
  rw [NetHack.Sokoban22Refined85.at164]
  rw [NetHack.Sokoban22Refined85.agree1503 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 164)))]
  change NetHack.Sokoban22Refined85.d1503 p = _
  exact oldNode1503 p
theorem oldAfter766 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 162 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 162))) = d48749 p := by
  rw [NetHack.Sokoban22Refined85.at162]
  rw [NetHack.Sokoban22Refined85.agree1150 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 162)))]
  change NetHack.Sokoban22Refined85.d1150 p = _
  exact oldNode1150 p
theorem oldAfter767 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 164 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 164))) = d49102 p := by
  rw [NetHack.Sokoban22Refined85.at164]
  rw [NetHack.Sokoban22Refined85.agree1503 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 164)))]
  change NetHack.Sokoban22Refined85.d1503 p = _
  exact oldNode1503 p
theorem oldAfter768 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 185 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 185))) = d49102 p := by
  rw [NetHack.Sokoban22Refined85.at185]
  rw [NetHack.Sokoban22Refined85.agree1503 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 185)))]
  change NetHack.Sokoban22Refined85.d1503 p = _
  exact oldNode1503 p
theorem oldAfter769 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 185 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 185 (.stay 184)))) = d49102 p := by
  rw [NetHack.Sokoban22Refined85.at185]
  rw [NetHack.Sokoban22Refined85.agree1503 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 185 (.stay 184))))]
  change NetHack.Sokoban22Refined85.d1503 (change p 185 (some 184)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 185 (some 184) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree1503 _ _ representative]
  change NetHack.Sokoban22Refined85.d1503 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub7977]
  exact oldNode1503 p
theorem oldAfter770 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 163 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 163))) = d48997 p := by
  rw [NetHack.Sokoban22Refined85.at163]
  rw [NetHack.Sokoban22Refined85.agree1398 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 163)))]
  change NetHack.Sokoban22Refined85.d1398 p = _
  exact oldNode1398 p
theorem oldAfter771 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 166 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 166))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at166]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 166)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter772 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 166 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 166 (.stay 144)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at166]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 166 (.stay 144))))]
  change NetHack.Sokoban22Refined85.d0 (change p 166 (some 144)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 166 (some 144) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter773 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 210 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 210))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at210]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 210)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter774 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 189 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 189))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at189]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 189)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter775 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 189 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 189 (.stay 190)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at189]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 189 (.stay 190))))]
  change NetHack.Sokoban22Refined85.d0 (change p 189 (some 190)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 189 (some 190) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter776 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 167 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 167))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at167]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 167)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter777 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 211 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 211))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at211]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 211)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter778 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 167 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 167))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at167]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 167)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter779 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 167 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 167 (.stay 145)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at167]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 167 (.stay 145))))]
  change NetHack.Sokoban22Refined85.d0 (change p 167 (some 145)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 167 (some 145) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter780 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 211 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 211))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at211]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 211)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter781 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 190 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 190))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at190]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 190)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter782 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 190 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 190 (.stay 191)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at190]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 190 (.stay 191))))]
  change NetHack.Sokoban22Refined85.d0 (change p 190 (some 191)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 190 (some 191) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter783 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 188 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 188))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at188]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 188)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter784 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 168 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 168))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at168]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 168)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter785 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 166 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 166))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at166]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 166)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter786 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 212 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 212))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at212]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 212)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter787 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 210 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 210))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at210]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 210)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter788 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 168 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 168))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at168]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 168)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter789 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 168 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 168 (.stay 146)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at168]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 168 (.stay 146))))]
  change NetHack.Sokoban22Refined85.d0 (change p 168 (some 146)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 168 (some 146) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter790 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 212 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 212))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at212]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 212)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter791 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 191 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 191))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at191]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 191)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter792 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 191 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 191 (.stay 192)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at191]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 191 (.stay 192))))]
  change NetHack.Sokoban22Refined85.d0 (change p 191 (some 192)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 191 (some 192) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter793 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 189 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 189))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at189]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 189)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter794 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 189 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 189 (.stay 188)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at189]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 189 (.stay 188))))]
  change NetHack.Sokoban22Refined85.d0 (change p 189 (some 188)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 189 (some 188) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter795 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 169 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 169))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at169]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 169)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter796 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 167 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 167))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at167]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 167)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter797 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 213 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 213))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at213]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 213)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter798 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 211 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 211))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at211]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 211)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter799 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 169 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 169))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at169]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 169)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
end NetHack.Soko22Hazard87
