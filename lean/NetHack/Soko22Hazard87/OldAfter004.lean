import NetHack.Soko22Hazard87.OldAfter003
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
namespace Prior
end Prior
theorem oldAfter320 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 127 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 127))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at127]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 127)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter321 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 89 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 89))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at89]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 89)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter322 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 89 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 89 (.stay 67)))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at89]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 89 (.stay 67))))]
  change NetHack.Sokoban22Refined85.d267 (change p 89 (some 67)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 89 (some 67) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree267 _ _ representative]
  change NetHack.Sokoban22Refined85.d267 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub267]
  exact oldNode267 p
theorem oldAfter323 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 133 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 133))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at133]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 133)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter324 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 133 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 133 (.stay 155)))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at133]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 133 (.stay 155))))]
  change NetHack.Sokoban22Refined85.d267 (change p 133 (some 155)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 133 (some 155) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree267 _ _ representative]
  change NetHack.Sokoban22Refined85.d267 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub267]
  exact oldNode267 p
theorem oldAfter325 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 90 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 90))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at90]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 90)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter326 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 134 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 134))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at134]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 134)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter327 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 91 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 91))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at91]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 91)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter328 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 91 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 91 (.stay 69)))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at91]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 91 (.stay 69))))]
  change NetHack.Sokoban22Refined85.d267 (change p 91 (some 69)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 91 (some 69) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree267 _ _ representative]
  change NetHack.Sokoban22Refined85.d267 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub267]
  exact oldNode267 p
theorem oldAfter329 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 135 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 135))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at135]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 135)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter330 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 135 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 135 (.stay 157)))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at135]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 135 (.stay 157))))]
  change NetHack.Sokoban22Refined85.d267 (change p 135 (some 157)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 135 (some 157) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree267 _ _ representative]
  change NetHack.Sokoban22Refined85.d267 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub267]
  exact oldNode267 p
theorem oldAfter331 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 114 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 114))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at114]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 114)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter332 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 114 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 114 (.stay 115)))) = d89607 p := by
  rw [NetHack.Sokoban22Refined85.at114]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 114 (.stay 115))))]
  change NetHack.Sokoban22Refined85.d267 (change p 114 (some 115)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 114 (some 115) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree267 _ _ representative]
  change NetHack.Sokoban22Refined85.d267 (change p 10000 (some 115)) = _
  rw [NetHack.Sokoban22Refined85.sub2500]
  exact oldNode4102 p
theorem oldAfter333 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 90 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 90))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at90]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 90)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter334 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 136 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 136))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at136]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 136)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter335 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 134 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 134))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at134]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 134)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter336 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 136 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 136))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at136]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 136)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter337 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 136 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 136 (.stay 158)))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at136]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 136 (.stay 158))))]
  change NetHack.Sokoban22Refined85.d267 (change p 136 (some 158)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 136 (some 158) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree267 _ _ representative]
  change NetHack.Sokoban22Refined85.d267 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub267]
  exact oldNode267 p
theorem oldAfter338 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 115 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 115))) = d48097 p := by
  rw [NetHack.Sokoban22Refined85.at115]
  rw [NetHack.Sokoban22Refined85.agree498 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 115)))]
  change NetHack.Sokoban22Refined85.d498 p = _
  exact oldNode498 p
theorem oldAfter339 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 115 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 115 (.stay 116)))) = d98796 p := by
  rw [NetHack.Sokoban22Refined85.at115]
  rw [NetHack.Sokoban22Refined85.agree498 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 115 (.stay 116))))]
  change NetHack.Sokoban22Refined85.d498 (change p 115 (some 116)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 115 (some 116) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree498 _ _ representative]
  change NetHack.Sokoban22Refined85.d498 (change p 115 (some 116)) = _
  rw [NetHack.Sokoban22Refined85.sub2631]
  exact oldNode4108 p
theorem oldAfter340 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 113 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 113))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at113]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 113)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter341 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 93 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 93))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at93]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 93)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter342 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 91 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 91))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at91]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 91)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter343 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 135 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 135))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at135]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 135)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter344 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 93 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 93))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at93]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 93)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter345 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 93 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 93 (.stay 71)))) = d99411 p := by
  rw [NetHack.Sokoban22Refined85.at93]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 93 (.stay 71))))]
  change NetHack.Sokoban22Refined85.d312 (change p 93 (some 71)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 93 (some 71) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree312 _ _ representative]
  change NetHack.Sokoban22Refined85.d312 (change p 10000 (some 71)) = _
  rw [NetHack.Sokoban22Refined85.sub2676]
  exact oldNode4110 p
theorem oldAfter346 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 116 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 116))) = d48115 p := by
  rw [NetHack.Sokoban22Refined85.at116]
  rw [NetHack.Sokoban22Refined85.agree516 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 116)))]
  change NetHack.Sokoban22Refined85.d516 p = _
  exact oldNode516 p
theorem oldAfter347 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 114 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 114))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at114]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 114)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter348 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 114 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 114 (.stay 113)))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at114]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 114 (.stay 113))))]
  change NetHack.Sokoban22Refined85.d267 (change p 114 (some 113)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 114 (some 113) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree267 _ _ representative]
  change NetHack.Sokoban22Refined85.d267 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub267]
  exact oldNode267 p
theorem oldAfter349 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 94 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 94))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at94]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 94)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter350 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 138 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 138))) = d48251 p := by
  rw [NetHack.Sokoban22Refined85.at138]
  rw [NetHack.Sokoban22Refined85.agree652 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 138)))]
  change NetHack.Sokoban22Refined85.d652 p = _
  exact oldNode652 p
theorem oldAfter351 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 136 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 136))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at136]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 136)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter352 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 94 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 94))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at94]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 94)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter353 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 138 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 138))) = d48251 p := by
  rw [NetHack.Sokoban22Refined85.at138]
  rw [NetHack.Sokoban22Refined85.agree652 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 138)))]
  change NetHack.Sokoban22Refined85.d652 p = _
  exact oldNode652 p
theorem oldAfter354 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 138 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 138 (.stay 160)))) = d100929 p := by
  rw [NetHack.Sokoban22Refined85.at138]
  rw [NetHack.Sokoban22Refined85.agree652 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 138 (.stay 160))))]
  change NetHack.Sokoban22Refined85.d652 (change p 138 (some 160)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 138 (some 160) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree652 _ _ representative]
  change NetHack.Sokoban22Refined85.d652 (change p 138 (some 160)) = _
  rw [NetHack.Sokoban22Refined85.sub2931]
  exact oldNode4141 p
theorem oldAfter355 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 115 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 115))) = d48097 p := by
  rw [NetHack.Sokoban22Refined85.at115]
  rw [NetHack.Sokoban22Refined85.agree498 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 115)))]
  change NetHack.Sokoban22Refined85.d498 p = _
  exact oldNode498 p
theorem oldAfter356 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 115 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 115 (.stay 114)))) = d100934 p := by
  rw [NetHack.Sokoban22Refined85.at115]
  rw [NetHack.Sokoban22Refined85.agree498 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 115 (.stay 114))))]
  change NetHack.Sokoban22Refined85.d498 (change p 115 (some 114)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 115 (some 114) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree498 _ _ representative]
  change NetHack.Sokoban22Refined85.d498 (change p 115 none) = _
  rw [NetHack.Sokoban22Refined85.sub3117]
  exact oldNode4146 p
theorem oldAfter357 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 95 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 95))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at95]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 95)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter358 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 93 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 93))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at93]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 93)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter359 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 96 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 96))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at96]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 96)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter360 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 96 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 96 (.stay 74)))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at96]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 96 (.stay 74))))]
  change NetHack.Sokoban22Refined85.d312 (change p 96 (some 74)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 96 (some 74) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree312 _ _ representative]
  change NetHack.Sokoban22Refined85.d312 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub412]
  exact oldNode312 p
theorem oldAfter361 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 119 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 119))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at119]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 119)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter362 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 119 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 119 (.stay 120)))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at119]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 119 (.stay 120))))]
  change NetHack.Sokoban22Refined85.d312 (change p 119 (some 120)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 119 (some 120) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree312 _ _ representative]
  change NetHack.Sokoban22Refined85.d312 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub412]
  exact oldNode312 p
theorem oldAfter363 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 97 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 97))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at97]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 97)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter364 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 95 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 95))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at95]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 95)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter365 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 141 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 141))) = d48308 p := by
  rw [NetHack.Sokoban22Refined85.at141]
  rw [NetHack.Sokoban22Refined85.agree709 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 141)))]
  change NetHack.Sokoban22Refined85.d709 p = _
  exact oldNode709 p
theorem oldAfter366 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 97 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 97))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at97]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 97)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter367 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 141 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 141))) = d48308 p := by
  rw [NetHack.Sokoban22Refined85.at141]
  rw [NetHack.Sokoban22Refined85.agree709 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 141)))]
  change NetHack.Sokoban22Refined85.d709 p = _
  exact oldNode709 p
theorem oldAfter368 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 141 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 141 (.stay 163)))) = d102102 p := by
  rw [NetHack.Sokoban22Refined85.at141]
  rw [NetHack.Sokoban22Refined85.agree709 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 141 (.stay 163))))]
  change NetHack.Sokoban22Refined85.d709 (change p 141 (some 163)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 141 (some 163) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree709 _ _ representative]
  change NetHack.Sokoban22Refined85.d709 (change p 141 (some 163)) = _
  rw [NetHack.Sokoban22Refined85.sub3281]
  exact oldNode4196 p
theorem oldAfter369 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 120 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 120))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at120]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 120)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter370 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 118 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 118))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at118]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 118)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter371 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 98 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 98))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at98]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 98)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter372 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 96 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 96))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at96]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 96)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter373 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 98 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 98))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at98]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 98)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter374 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 98 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 98 (.stay 76)))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at98]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 98 (.stay 76))))]
  change NetHack.Sokoban22Refined85.d312 (change p 98 (some 76)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 98 (some 76) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree312 _ _ representative]
  change NetHack.Sokoban22Refined85.d312 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub412]
  exact oldNode312 p
theorem oldAfter375 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 119 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 119))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at119]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 119)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter376 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 119 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 119 (.stay 118)))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at119]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 119 (.stay 118))))]
  change NetHack.Sokoban22Refined85.d312 (change p 119 (some 118)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 119 (some 118) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree312 _ _ representative]
  change NetHack.Sokoban22Refined85.d312 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub412]
  exact oldNode312 p
theorem oldAfter377 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 97 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 97))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at97]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 97)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter378 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 141 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 141))) = d48308 p := by
  rw [NetHack.Sokoban22Refined85.at141]
  rw [NetHack.Sokoban22Refined85.agree709 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 141)))]
  change NetHack.Sokoban22Refined85.d709 p = _
  exact oldNode709 p
theorem oldAfter379 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 100 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 100))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at100]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 100)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter380 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 100 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 100 (.stay 78)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at100]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 100 (.stay 78))))]
  change NetHack.Sokoban22Refined85.d0 (change p 100 (some 78)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 100 (some 78) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter381 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 144 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 144))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at144]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 144)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter382 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 144 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 144 (.stay 166)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at144]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 144 (.stay 166))))]
  change NetHack.Sokoban22Refined85.d0 (change p 144 (some 166)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 144 (some 166) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter383 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 123 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 123))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at123]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 123)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter384 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 123 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 123 (.stay 124)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at123]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 123 (.stay 124))))]
  change NetHack.Sokoban22Refined85.d0 (change p 123 (some 124)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 123 (some 124) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter385 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 101 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 101))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at101]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 101)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter386 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 145 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 145))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at145]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 145)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter387 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 101 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 101))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at101]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 101)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter388 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 101 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 101 (.stay 79)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at101]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 101 (.stay 79))))]
  change NetHack.Sokoban22Refined85.d0 (change p 101 (some 79)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 101 (some 79) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter389 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 145 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 145))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at145]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 145)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter390 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 145 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 145 (.stay 167)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at145]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 145 (.stay 167))))]
  change NetHack.Sokoban22Refined85.d0 (change p 145 (some 167)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 145 (some 167) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter391 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 124 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 124))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at124]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 124)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter392 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 124 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 124 (.stay 125)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at124]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 124 (.stay 125))))]
  change NetHack.Sokoban22Refined85.d0 (change p 124 (some 125)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 124 (some 125) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
theorem oldAfter393 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 122 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 122))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at122]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 122)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter394 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 102 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 102))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at102]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 102)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter395 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 100 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 100))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at100]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 100)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter396 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 146 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 146))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at146]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 146)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter397 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 144 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 144))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at144]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 144)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter398 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 102 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 102))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at102]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 102)))]
  change NetHack.Sokoban22Refined85.d0 p = _
  exact oldNode0 p
theorem oldAfter399 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 102 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 102 (.stay 80)))) = d0 p := by
  rw [NetHack.Sokoban22Refined85.at102]
  rw [NetHack.Sokoban22Refined85.agree0 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 102 (.stay 80))))]
  change NetHack.Sokoban22Refined85.d0 (change p 102 (some 80)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 102 (some 80) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree0 _ _ representative]
  change NetHack.Sokoban22Refined85.d0 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub0]
  exact oldNode0 p
end NetHack.Soko22Hazard87
