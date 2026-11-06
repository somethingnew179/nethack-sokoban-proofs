import NetHack.Soko22Hazard87.OldNodes019
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
namespace Prior
end Prior
theorem oldAfter0 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 47 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 47))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at47]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 47)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter1 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 47 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 47 (.stay 69)))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at47]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 47 (.stay 69))))]
  change NetHack.Sokoban22Refined85.d267 (change p 47 (some 69)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 47 (some 69) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree267 _ _ representative]
  change NetHack.Sokoban22Refined85.d267 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub267]
  exact oldNode267 p
theorem oldAfter2 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 48 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 48))) = d48080 p := by
  rw [NetHack.Sokoban22Refined85.at48]
  rw [NetHack.Sokoban22Refined85.agree481 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 48)))]
  change NetHack.Sokoban22Refined85.d481 p = _
  exact oldNode481 p
theorem oldAfter3 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 46 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 46))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at46]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 46)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter4 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 49 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 49))) = d48083 p := by
  rw [NetHack.Sokoban22Refined85.at49]
  rw [NetHack.Sokoban22Refined85.agree484 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 49)))]
  change NetHack.Sokoban22Refined85.d484 p = _
  exact oldNode484 p
theorem oldAfter5 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 49 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 49 (.stay 71)))) = d47700 p := by
  rw [NetHack.Sokoban22Refined85.at49]
  rw [NetHack.Sokoban22Refined85.agree484 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 49 (.stay 71))))]
  change NetHack.Sokoban22Refined85.d484 (change p 49 (some 71)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 49 (some 71) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree484 _ _ representative]
  change NetHack.Sokoban22Refined85.d484 (change p 49 (some 71)) = _
  rw [NetHack.Sokoban22Refined85.sub367]
  exact oldNode101 p
theorem oldAfter6 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 28 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 28))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at28]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 28)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter7 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 28 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 28 (.stay 29)))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at28]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 28 (.stay 29))))]
  change NetHack.Sokoban22Refined85.d312 (change p 28 (some 29)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 28 (some 29) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree312 _ _ representative]
  change NetHack.Sokoban22Refined85.d312 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub412]
  exact oldNode312 p
theorem oldAfter8 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 50 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 50))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at50]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 50)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter9 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 48 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 48))) = d48080 p := by
  rw [NetHack.Sokoban22Refined85.at48]
  rw [NetHack.Sokoban22Refined85.agree481 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 48)))]
  change NetHack.Sokoban22Refined85.d481 p = _
  exact oldNode481 p
theorem oldAfter10 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 50 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 50))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at50]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 50)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter11 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 29 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 29))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at29]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 29)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter12 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 29 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 29 (.stay 30)))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at29]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 29 (.stay 30))))]
  change NetHack.Sokoban22Refined85.d312 (change p 29 (some 30)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 29 (some 30) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree312 _ _ representative]
  change NetHack.Sokoban22Refined85.d312 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub412]
  exact oldNode312 p
theorem oldAfter13 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 27 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 27))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at27]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 27)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter14 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 51 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 51))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at51]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 51)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter15 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 49 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 49))) = d48083 p := by
  rw [NetHack.Sokoban22Refined85.at49]
  rw [NetHack.Sokoban22Refined85.agree484 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 49)))]
  change NetHack.Sokoban22Refined85.d484 p = _
  exact oldNode484 p
theorem oldAfter16 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 51 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 51))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at51]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 51)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter17 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 51 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 51 (.stay 73)))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at51]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 51 (.stay 73))))]
  change NetHack.Sokoban22Refined85.d312 (change p 51 (some 73)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 51 (some 73) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree312 _ _ representative]
  change NetHack.Sokoban22Refined85.d312 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub412]
  exact oldNode312 p
theorem oldAfter18 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 30 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 30))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at30]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 30)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter19 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 28 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 28))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at28]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 28)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter20 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 28 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 28 (.stay 27)))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at28]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 28 (.stay 27))))]
  change NetHack.Sokoban22Refined85.d312 (change p 28 (some 27)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 28 (some 27) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree312 _ _ representative]
  change NetHack.Sokoban22Refined85.d312 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub412]
  exact oldNode312 p
theorem oldAfter21 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 52 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 52))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at52]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 52)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter22 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 50 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 50))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at50]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 50)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter23 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 52 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 52))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at52]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 52)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter24 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 52 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 52 (.stay 74)))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at52]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 52 (.stay 74))))]
  change NetHack.Sokoban22Refined85.d312 (change p 52 (some 74)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 52 (some 74) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree312 _ _ representative]
  change NetHack.Sokoban22Refined85.d312 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub412]
  exact oldNode312 p
theorem oldAfter25 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 29 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 29))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at29]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 29)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter26 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 29 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 29 (.stay 28)))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at29]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 29 (.stay 28))))]
  change NetHack.Sokoban22Refined85.d312 (change p 29 (some 28)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 29 (some 28) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree312 _ _ representative]
  change NetHack.Sokoban22Refined85.d312 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub412]
  exact oldNode312 p
theorem oldAfter27 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 51 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 51))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at51]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 51)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter28 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 67 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 67))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at67]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 67)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter29 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 67 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 67 (.stay 89)))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at67]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 67 (.stay 89))))]
  change NetHack.Sokoban22Refined85.d267 (change p 67 (some 89)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 67 (some 89) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree267 _ _ representative]
  change NetHack.Sokoban22Refined85.d267 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub267]
  exact oldNode267 p
theorem oldAfter30 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 46 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 46))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at46]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 46)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter31 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 46 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 46 (.stay 47)))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at46]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 46 (.stay 47))))]
  change NetHack.Sokoban22Refined85.d267 (change p 46 (some 47)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 46 (some 47) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree267 _ _ representative]
  change NetHack.Sokoban22Refined85.d267 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub267]
  exact oldNode267 p
theorem oldAfter32 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 47 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 47))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at47]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 47)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter33 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 47 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 47 (.stay 48)))) = d47865 p := by
  rw [NetHack.Sokoban22Refined85.at47]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 47 (.stay 48))))]
  change NetHack.Sokoban22Refined85.d267 (change p 47 (some 48)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 47 (some 48) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree267 _ _ representative]
  change NetHack.Sokoban22Refined85.d267 (change p 10000 (some 48)) = _
  rw [NetHack.Sokoban22Refined85.sub660]
  exact oldNode266 p
theorem oldAfter34 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 45 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 45))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at45]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 45)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter35 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 25 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 25))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at25]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 25)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter36 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 69 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 69))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at69]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 69)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter37 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 67 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 67))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at67]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 67)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter38 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 25 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 25))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at25]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 25)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter39 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 69 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 69))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at69]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 69)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter40 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 69 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 69 (.stay 91)))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at69]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 69 (.stay 91))))]
  change NetHack.Sokoban22Refined85.d267 (change p 69 (some 91)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 69 (some 91) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree267 _ _ representative]
  change NetHack.Sokoban22Refined85.d267 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub267]
  exact oldNode267 p
theorem oldAfter41 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 48 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 48))) = d48080 p := by
  rw [NetHack.Sokoban22Refined85.at48]
  rw [NetHack.Sokoban22Refined85.agree481 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 48)))]
  change NetHack.Sokoban22Refined85.d481 p = _
  exact oldNode481 p
theorem oldAfter42 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 48 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 48 (.stay 49)))) = d47767 p := by
  rw [NetHack.Sokoban22Refined85.at48]
  rw [NetHack.Sokoban22Refined85.agree481 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 48 (.stay 49))))]
  change NetHack.Sokoban22Refined85.d481 (change p 48 (some 49)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 48 (some 49) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree481 _ _ representative]
  change NetHack.Sokoban22Refined85.d481 (change p 48 (some 49)) = _
  rw [NetHack.Sokoban22Refined85.sub830]
  exact oldNode168 p
theorem oldAfter43 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 46 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 46))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at46]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 46)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter44 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 46 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 46 (.stay 45)))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at46]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 46 (.stay 45))))]
  change NetHack.Sokoban22Refined85.d267 (change p 46 (some 45)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 46 (some 45) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree267 _ _ representative]
  change NetHack.Sokoban22Refined85.d267 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub267]
  exact oldNode267 p
theorem oldAfter45 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 70 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 70))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at70]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 70)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter46 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 70 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 70))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at70]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 70)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter47 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 49 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 49))) = d48083 p := by
  rw [NetHack.Sokoban22Refined85.at49]
  rw [NetHack.Sokoban22Refined85.agree484 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 49)))]
  change NetHack.Sokoban22Refined85.d484 p = _
  exact oldNode484 p
theorem oldAfter48 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 49 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 49 (.stay 50)))) = d47700 p := by
  rw [NetHack.Sokoban22Refined85.at49]
  rw [NetHack.Sokoban22Refined85.agree484 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 49 (.stay 50))))]
  change NetHack.Sokoban22Refined85.d484 (change p 49 (some 50)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 49 (some 50) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree484 _ _ representative]
  change NetHack.Sokoban22Refined85.d484 (change p 49 none) = _
  rw [NetHack.Sokoban22Refined85.sub930]
  exact oldNode101 p
theorem oldAfter49 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 47 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 47))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at47]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 47)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter50 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 47 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 47 (.stay 46)))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at47]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 47 (.stay 46))))]
  change NetHack.Sokoban22Refined85.d267 (change p 47 (some 46)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 47 (some 46) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree267 _ _ representative]
  change NetHack.Sokoban22Refined85.d267 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub267]
  exact oldNode267 p
theorem oldAfter51 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 27 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 27))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at27]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 27)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter52 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 25 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 25))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at25]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 25)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter53 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 71 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 71))) = d48087 p := by
  rw [NetHack.Sokoban22Refined85.at71]
  rw [NetHack.Sokoban22Refined85.agree488 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 71)))]
  change NetHack.Sokoban22Refined85.d488 p = _
  exact oldNode488 p
theorem oldAfter54 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 69 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 69))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at69]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 69)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter55 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 27 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 27))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at27]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 27)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter56 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 71 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 71))) = d48087 p := by
  rw [NetHack.Sokoban22Refined85.at71]
  rw [NetHack.Sokoban22Refined85.agree488 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 71)))]
  change NetHack.Sokoban22Refined85.d488 p = _
  exact oldNode488 p
theorem oldAfter57 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 71 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 71 (.stay 93)))) = d47700 p := by
  rw [NetHack.Sokoban22Refined85.at71]
  rw [NetHack.Sokoban22Refined85.agree488 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 71 (.stay 93))))]
  change NetHack.Sokoban22Refined85.d488 (change p 71 (some 93)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 71 (some 93) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree488 _ _ representative]
  change NetHack.Sokoban22Refined85.d488 (change p 71 none) = _
  rw [NetHack.Sokoban22Refined85.sub1031]
  exact oldNode101 p
theorem oldAfter58 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 50 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 50))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at50]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 50)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter59 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 50 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 50 (.stay 51)))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at50]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 50 (.stay 51))))]
  change NetHack.Sokoban22Refined85.d312 (change p 50 (some 51)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 50 (some 51) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree312 _ _ representative]
  change NetHack.Sokoban22Refined85.d312 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub412]
  exact oldNode312 p
theorem oldAfter60 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 48 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 48))) = d48080 p := by
  rw [NetHack.Sokoban22Refined85.at48]
  rw [NetHack.Sokoban22Refined85.agree481 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 48)))]
  change NetHack.Sokoban22Refined85.d481 p = _
  exact oldNode481 p
theorem oldAfter61 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 48 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 48 (.stay 47)))) = d47768 p := by
  rw [NetHack.Sokoban22Refined85.at48]
  rw [NetHack.Sokoban22Refined85.agree481 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 48 (.stay 47))))]
  change NetHack.Sokoban22Refined85.d481 (change p 48 (some 47)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 48 (some 47) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree481 _ _ representative]
  change NetHack.Sokoban22Refined85.d481 (change p 48 none) = _
  rw [NetHack.Sokoban22Refined85.sub1201]
  exact oldNode169 p
theorem oldAfter62 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 28 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 28))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at28]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 28)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter63 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 70 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 70))) = d47866 p := by
  rw [NetHack.Sokoban22Refined85.at70]
  rw [NetHack.Sokoban22Refined85.agree267 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 70)))]
  change NetHack.Sokoban22Refined85.d267 p = _
  exact oldNode267 p
theorem oldAfter64 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 28 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 28))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at28]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 28)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter65 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 51 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 51))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at51]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 51)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter66 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 51 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 51 (.stay 52)))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at51]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 51 (.stay 52))))]
  change NetHack.Sokoban22Refined85.d312 (change p 51 (some 52)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 51 (some 52) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree312 _ _ representative]
  change NetHack.Sokoban22Refined85.d312 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub412]
  exact oldNode312 p
theorem oldAfter67 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 49 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 49))) = d48083 p := by
  rw [NetHack.Sokoban22Refined85.at49]
  rw [NetHack.Sokoban22Refined85.agree484 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 49)))]
  change NetHack.Sokoban22Refined85.d484 p = _
  exact oldNode484 p
theorem oldAfter68 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 49 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 49 (.stay 48)))) = d47700 p := by
  rw [NetHack.Sokoban22Refined85.at49]
  rw [NetHack.Sokoban22Refined85.agree484 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 49 (.stay 48))))]
  change NetHack.Sokoban22Refined85.d484 (change p 49 (some 48)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 49 (some 48) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree484 _ _ representative]
  change NetHack.Sokoban22Refined85.d484 (change p 49 (some 48)) = _
  rw [NetHack.Sokoban22Refined85.sub1300]
  exact oldNode101 p
theorem oldAfter69 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 29 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 29))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at29]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 29)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter70 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 27 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 27))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at27]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 27)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter71 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 73 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 73))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at73]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 73)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter72 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 71 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 71))) = d48087 p := by
  rw [NetHack.Sokoban22Refined85.at71]
  rw [NetHack.Sokoban22Refined85.agree488 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 71)))]
  change NetHack.Sokoban22Refined85.d488 p = _
  exact oldNode488 p
theorem oldAfter73 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 29 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 29))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at29]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 29)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter74 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 73 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 73))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at73]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 73)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter75 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 73 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 73 (.stay 95)))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at73]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 73 (.stay 95))))]
  change NetHack.Sokoban22Refined85.d312 (change p 73 (some 95)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 73 (some 95) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree312 _ _ representative]
  change NetHack.Sokoban22Refined85.d312 (change p 10000 none) = _
  rw [NetHack.Sokoban22Refined85.sub412]
  exact oldNode312 p
theorem oldAfter76 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 52 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 52))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at52]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 52)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter77 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 50 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 50))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at50]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 50)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
theorem oldAfter78 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 50 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.push 50 (.stay 49)))) = d65730 p := by
  rw [NetHack.Sokoban22Refined85.at50]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.push 50 (.stay 49))))]
  change NetHack.Sokoban22Refined85.d312 (change p 50 (some 49)) = _
  have representative := change_representative NetHack.Sokoban22Refined85.support p 50 (some 49) 10000 prior_dummy
  rw [NetHack.Sokoban22Refined85.agree312 _ _ representative]
  change NetHack.Sokoban22Refined85.d312 (change p 10000 (some 49)) = _
  rw [NetHack.Sokoban22Refined85.sub1529]
  exact oldNode4053 p
theorem oldAfter79 (p : Pattern) : NetHack.Sokoban22Refined85.bonus 30 (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p (.walk 30))) = d47911 p := by
  rw [NetHack.Sokoban22Refined85.at30]
  rw [NetHack.Sokoban22Refined85.agree312 _ _ (prior_box_agree (HazardPattern.afterPattern 10000 p (.walk 30)))]
  change NetHack.Sokoban22Refined85.d312 p = _
  exact oldNode312 p
end NetHack.Soko22Hazard87
