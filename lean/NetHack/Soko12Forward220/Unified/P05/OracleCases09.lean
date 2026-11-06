import NetHack.Soko12Forward220.Unified.P05.OracleCases08
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P05
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
noncomputable def rowCases450 : List PhysicalCase := []
theorem rowFits450 : ∀ entry ∈ rowCases450, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked450 : ∀ entry ∈ rowCases450, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero450 : ∀ entry ∈ rowCases450, entry.hero = 220 := by exact (by intro entry member; cases member)
theorem rowDirection450 : ∀ entry ∈ rowCases450, entry.direction = .east := by exact (by intro entry member; cases member)
theorem rowPhase450 : ∀ entry ∈ rowCases450, entry.phase = 5 := by exact (by intro entry member; cases member)
noncomputable def rowCases451 : List PhysicalCase := [case398, case787]
theorem memberCase398 : case398 ∈ rowCases451 := by exact List.mem_cons_self
theorem memberCase787 : case787 ∈ rowCases451 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits451 : ∀ entry ∈ rowCases451, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case398_fitted, (List.forall_mem_cons.mpr ⟨case787_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked451 : ∀ entry ∈ rowCases451, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame398_checked, (List.forall_mem_cons.mpr ⟨frame787_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero451 : ∀ entry ∈ rowCases451, entry.hero = 220 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection451 : ∀ entry ∈ rowCases451, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase451 : ∀ entry ∈ rowCases451, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases452 : List PhysicalCase := []
theorem rowFits452 : ∀ entry ∈ rowCases452, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked452 : ∀ entry ∈ rowCases452, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero452 : ∀ entry ∈ rowCases452, entry.hero = 220 := by exact (by intro entry member; cases member)
theorem rowDirection452 : ∀ entry ∈ rowCases452, entry.direction = .northEast := by exact (by intro entry member; cases member)
theorem rowPhase452 : ∀ entry ∈ rowCases452, entry.phase = 5 := by exact (by intro entry member; cases member)
noncomputable def rowCases453 : List PhysicalCase := [case399, case400]
theorem memberCase399 : case399 ∈ rowCases453 := by exact List.mem_cons_self
theorem memberCase400 : case400 ∈ rowCases453 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits453 : ∀ entry ∈ rowCases453, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case399_fitted, (List.forall_mem_cons.mpr ⟨case400_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked453 : ∀ entry ∈ rowCases453, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame399_checked, (List.forall_mem_cons.mpr ⟨frame400_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero453 : ∀ entry ∈ rowCases453, entry.hero = 220 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection453 : ∀ entry ∈ rowCases453, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase453 : ∀ entry ∈ rowCases453, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases454 : List PhysicalCase := []
theorem rowFits454 : ∀ entry ∈ rowCases454, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked454 : ∀ entry ∈ rowCases454, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero454 : ∀ entry ∈ rowCases454, entry.hero = 220 := by exact (by intro entry member; cases member)
theorem rowDirection454 : ∀ entry ∈ rowCases454, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase454 : ∀ entry ∈ rowCases454, entry.phase = 5 := by exact (by intro entry member; cases member)
noncomputable def rowCases455 : List PhysicalCase := [case401, case402]
theorem memberCase401 : case401 ∈ rowCases455 := by exact List.mem_cons_self
theorem memberCase402 : case402 ∈ rowCases455 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits455 : ∀ entry ∈ rowCases455, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case401_fitted, (List.forall_mem_cons.mpr ⟨case402_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked455 : ∀ entry ∈ rowCases455, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame401_checked, (List.forall_mem_cons.mpr ⟨frame402_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero455 : ∀ entry ∈ rowCases455, entry.hero = 220 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection455 : ∀ entry ∈ rowCases455, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase455 : ∀ entry ∈ rowCases455, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases456 : List PhysicalCase := [case403, case760]
theorem memberCase403 : case403 ∈ rowCases456 := by exact List.mem_cons_self
theorem memberCase760 : case760 ∈ rowCases456 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits456 : ∀ entry ∈ rowCases456, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case403_fitted, (List.forall_mem_cons.mpr ⟨case760_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked456 : ∀ entry ∈ rowCases456, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame403_checked, (List.forall_mem_cons.mpr ⟨frame760_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero456 : ∀ entry ∈ rowCases456, entry.hero = 236 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection456 : ∀ entry ∈ rowCases456, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase456 : ∀ entry ∈ rowCases456, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases457 : List PhysicalCase := [case404, case811]
theorem memberCase404 : case404 ∈ rowCases457 := by exact List.mem_cons_self
theorem memberCase811 : case811 ∈ rowCases457 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits457 : ∀ entry ∈ rowCases457, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case404_fitted, (List.forall_mem_cons.mpr ⟨case811_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked457 : ∀ entry ∈ rowCases457, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame404_checked, (List.forall_mem_cons.mpr ⟨frame811_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero457 : ∀ entry ∈ rowCases457, entry.hero = 236 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection457 : ∀ entry ∈ rowCases457, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase457 : ∀ entry ∈ rowCases457, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases458 : List PhysicalCase := [case405, case794]
theorem memberCase405 : case405 ∈ rowCases458 := by exact List.mem_cons_self
theorem memberCase794 : case794 ∈ rowCases458 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits458 : ∀ entry ∈ rowCases458, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case405_fitted, (List.forall_mem_cons.mpr ⟨case794_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked458 : ∀ entry ∈ rowCases458, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame405_checked, (List.forall_mem_cons.mpr ⟨frame794_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero458 : ∀ entry ∈ rowCases458, entry.hero = 236 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection458 : ∀ entry ∈ rowCases458, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase458 : ∀ entry ∈ rowCases458, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases459 : List PhysicalCase := []
theorem rowFits459 : ∀ entry ∈ rowCases459, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked459 : ∀ entry ∈ rowCases459, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero459 : ∀ entry ∈ rowCases459, entry.hero = 236 := by exact (by intro entry member; cases member)
theorem rowDirection459 : ∀ entry ∈ rowCases459, entry.direction = .west := by exact (by intro entry member; cases member)
theorem rowPhase459 : ∀ entry ∈ rowCases459, entry.phase = 5 := by exact (by intro entry member; cases member)
noncomputable def rowCases460 : List PhysicalCase := [case406, case407]
theorem memberCase406 : case406 ∈ rowCases460 := by exact List.mem_cons_self
theorem memberCase407 : case407 ∈ rowCases460 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits460 : ∀ entry ∈ rowCases460, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case406_fitted, (List.forall_mem_cons.mpr ⟨case407_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked460 : ∀ entry ∈ rowCases460, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame406_checked, (List.forall_mem_cons.mpr ⟨frame407_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero460 : ∀ entry ∈ rowCases460, entry.hero = 236 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection460 : ∀ entry ∈ rowCases460, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase460 : ∀ entry ∈ rowCases460, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases461 : List PhysicalCase := []
theorem rowFits461 : ∀ entry ∈ rowCases461, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked461 : ∀ entry ∈ rowCases461, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero461 : ∀ entry ∈ rowCases461, entry.hero = 236 := by exact (by intro entry member; cases member)
theorem rowDirection461 : ∀ entry ∈ rowCases461, entry.direction = .northWest := by exact (by intro entry member; cases member)
theorem rowPhase461 : ∀ entry ∈ rowCases461, entry.phase = 5 := by exact (by intro entry member; cases member)
noncomputable def rowCases462 : List PhysicalCase := [case408, case409]
theorem memberCase408 : case408 ∈ rowCases462 := by exact List.mem_cons_self
theorem memberCase409 : case409 ∈ rowCases462 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits462 : ∀ entry ∈ rowCases462, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case408_fitted, (List.forall_mem_cons.mpr ⟨case409_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked462 : ∀ entry ∈ rowCases462, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame408_checked, (List.forall_mem_cons.mpr ⟨frame409_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero462 : ∀ entry ∈ rowCases462, entry.hero = 236 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection462 : ∀ entry ∈ rowCases462, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase462 : ∀ entry ∈ rowCases462, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases463 : List PhysicalCase := []
theorem rowFits463 : ∀ entry ∈ rowCases463, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked463 : ∀ entry ∈ rowCases463, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero463 : ∀ entry ∈ rowCases463, entry.hero = 236 := by exact (by intro entry member; cases member)
theorem rowDirection463 : ∀ entry ∈ rowCases463, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase463 : ∀ entry ∈ rowCases463, entry.phase = 5 := by exact (by intro entry member; cases member)
noncomputable def rowCases464 : List PhysicalCase := [case410, case762]
theorem memberCase410 : case410 ∈ rowCases464 := by exact List.mem_cons_self
theorem memberCase762 : case762 ∈ rowCases464 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits464 : ∀ entry ∈ rowCases464, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case410_fitted, (List.forall_mem_cons.mpr ⟨case762_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked464 : ∀ entry ∈ rowCases464, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame410_checked, (List.forall_mem_cons.mpr ⟨frame762_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero464 : ∀ entry ∈ rowCases464, entry.hero = 237 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection464 : ∀ entry ∈ rowCases464, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase464 : ∀ entry ∈ rowCases464, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases465 : List PhysicalCase := [case411, case813]
theorem memberCase411 : case411 ∈ rowCases465 := by exact List.mem_cons_self
theorem memberCase813 : case813 ∈ rowCases465 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits465 : ∀ entry ∈ rowCases465, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case411_fitted, (List.forall_mem_cons.mpr ⟨case813_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked465 : ∀ entry ∈ rowCases465, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame411_checked, (List.forall_mem_cons.mpr ⟨frame813_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero465 : ∀ entry ∈ rowCases465, entry.hero = 237 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection465 : ∀ entry ∈ rowCases465, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase465 : ∀ entry ∈ rowCases465, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases466 : List PhysicalCase := [case412, case798]
theorem memberCase412 : case412 ∈ rowCases466 := by exact List.mem_cons_self
theorem memberCase798 : case798 ∈ rowCases466 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits466 : ∀ entry ∈ rowCases466, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case412_fitted, (List.forall_mem_cons.mpr ⟨case798_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked466 : ∀ entry ∈ rowCases466, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame412_checked, (List.forall_mem_cons.mpr ⟨frame798_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero466 : ∀ entry ∈ rowCases466, entry.hero = 237 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection466 : ∀ entry ∈ rowCases466, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase466 : ∀ entry ∈ rowCases466, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases467 : List PhysicalCase := [case413]
theorem memberCase413 : case413 ∈ rowCases467 := by exact List.mem_cons_self
theorem rowFits467 : ∀ entry ∈ rowCases467, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case413_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked467 : ∀ entry ∈ rowCases467, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame413_checked, (by intro entry member; cases member)⟩)
theorem rowHero467 : ∀ entry ∈ rowCases467, entry.hero = 237 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection467 : ∀ entry ∈ rowCases467, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase467 : ∀ entry ∈ rowCases467, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases468 : List PhysicalCase := [case414, case415]
theorem memberCase414 : case414 ∈ rowCases468 := by exact List.mem_cons_self
theorem memberCase415 : case415 ∈ rowCases468 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits468 : ∀ entry ∈ rowCases468, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case414_fitted, (List.forall_mem_cons.mpr ⟨case415_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked468 : ∀ entry ∈ rowCases468, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame414_checked, (List.forall_mem_cons.mpr ⟨frame415_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero468 : ∀ entry ∈ rowCases468, entry.hero = 237 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection468 : ∀ entry ∈ rowCases468, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase468 : ∀ entry ∈ rowCases468, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases469 : List PhysicalCase := [case416, case417]
theorem memberCase416 : case416 ∈ rowCases469 := by exact List.mem_cons_self
theorem memberCase417 : case417 ∈ rowCases469 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits469 : ∀ entry ∈ rowCases469, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case416_fitted, (List.forall_mem_cons.mpr ⟨case417_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked469 : ∀ entry ∈ rowCases469, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame416_checked, (List.forall_mem_cons.mpr ⟨frame417_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero469 : ∀ entry ∈ rowCases469, entry.hero = 237 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection469 : ∀ entry ∈ rowCases469, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase469 : ∀ entry ∈ rowCases469, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases470 : List PhysicalCase := [case418, case419]
theorem memberCase418 : case418 ∈ rowCases470 := by exact List.mem_cons_self
theorem memberCase419 : case419 ∈ rowCases470 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits470 : ∀ entry ∈ rowCases470, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case418_fitted, (List.forall_mem_cons.mpr ⟨case419_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked470 : ∀ entry ∈ rowCases470, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame418_checked, (List.forall_mem_cons.mpr ⟨frame419_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero470 : ∀ entry ∈ rowCases470, entry.hero = 237 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection470 : ∀ entry ∈ rowCases470, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase470 : ∀ entry ∈ rowCases470, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases471 : List PhysicalCase := [case420, case421]
theorem memberCase420 : case420 ∈ rowCases471 := by exact List.mem_cons_self
theorem memberCase421 : case421 ∈ rowCases471 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits471 : ∀ entry ∈ rowCases471, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case420_fitted, (List.forall_mem_cons.mpr ⟨case421_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked471 : ∀ entry ∈ rowCases471, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame420_checked, (List.forall_mem_cons.mpr ⟨frame421_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero471 : ∀ entry ∈ rowCases471, entry.hero = 237 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection471 : ∀ entry ∈ rowCases471, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase471 : ∀ entry ∈ rowCases471, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases472 : List PhysicalCase := [case422, case766]
theorem memberCase422 : case422 ∈ rowCases472 := by exact List.mem_cons_self
theorem memberCase766 : case766 ∈ rowCases472 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits472 : ∀ entry ∈ rowCases472, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case422_fitted, (List.forall_mem_cons.mpr ⟨case766_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked472 : ∀ entry ∈ rowCases472, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame422_checked, (List.forall_mem_cons.mpr ⟨frame766_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero472 : ∀ entry ∈ rowCases472, entry.hero = 238 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection472 : ∀ entry ∈ rowCases472, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase472 : ∀ entry ∈ rowCases472, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases473 : List PhysicalCase := [case423, case817]
theorem memberCase423 : case423 ∈ rowCases473 := by exact List.mem_cons_self
theorem memberCase817 : case817 ∈ rowCases473 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits473 : ∀ entry ∈ rowCases473, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case423_fitted, (List.forall_mem_cons.mpr ⟨case817_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked473 : ∀ entry ∈ rowCases473, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame423_checked, (List.forall_mem_cons.mpr ⟨frame817_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero473 : ∀ entry ∈ rowCases473, entry.hero = 238 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection473 : ∀ entry ∈ rowCases473, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase473 : ∀ entry ∈ rowCases473, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases474 : List PhysicalCase := [case424]
theorem memberCase424 : case424 ∈ rowCases474 := by exact List.mem_cons_self
theorem rowFits474 : ∀ entry ∈ rowCases474, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case424_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked474 : ∀ entry ∈ rowCases474, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame424_checked, (by intro entry member; cases member)⟩)
theorem rowHero474 : ∀ entry ∈ rowCases474, entry.hero = 238 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection474 : ∀ entry ∈ rowCases474, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase474 : ∀ entry ∈ rowCases474, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases475 : List PhysicalCase := [case425, case795]
theorem memberCase425 : case425 ∈ rowCases475 := by exact List.mem_cons_self
theorem memberCase795 : case795 ∈ rowCases475 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits475 : ∀ entry ∈ rowCases475, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case425_fitted, (List.forall_mem_cons.mpr ⟨case795_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked475 : ∀ entry ∈ rowCases475, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame425_checked, (List.forall_mem_cons.mpr ⟨frame795_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero475 : ∀ entry ∈ rowCases475, entry.hero = 238 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection475 : ∀ entry ∈ rowCases475, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase475 : ∀ entry ∈ rowCases475, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases476 : List PhysicalCase := [case426, case427]
theorem memberCase426 : case426 ∈ rowCases476 := by exact List.mem_cons_self
theorem memberCase427 : case427 ∈ rowCases476 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits476 : ∀ entry ∈ rowCases476, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case426_fitted, (List.forall_mem_cons.mpr ⟨case427_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked476 : ∀ entry ∈ rowCases476, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame426_checked, (List.forall_mem_cons.mpr ⟨frame427_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero476 : ∀ entry ∈ rowCases476, entry.hero = 238 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection476 : ∀ entry ∈ rowCases476, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase476 : ∀ entry ∈ rowCases476, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases477 : List PhysicalCase := [case428, case429]
theorem memberCase428 : case428 ∈ rowCases477 := by exact List.mem_cons_self
theorem memberCase429 : case429 ∈ rowCases477 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits477 : ∀ entry ∈ rowCases477, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case428_fitted, (List.forall_mem_cons.mpr ⟨case429_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked477 : ∀ entry ∈ rowCases477, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame428_checked, (List.forall_mem_cons.mpr ⟨frame429_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero477 : ∀ entry ∈ rowCases477, entry.hero = 238 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection477 : ∀ entry ∈ rowCases477, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase477 : ∀ entry ∈ rowCases477, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases478 : List PhysicalCase := [case430, case431]
theorem memberCase430 : case430 ∈ rowCases478 := by exact List.mem_cons_self
theorem memberCase431 : case431 ∈ rowCases478 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits478 : ∀ entry ∈ rowCases478, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case430_fitted, (List.forall_mem_cons.mpr ⟨case431_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked478 : ∀ entry ∈ rowCases478, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame430_checked, (List.forall_mem_cons.mpr ⟨frame431_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero478 : ∀ entry ∈ rowCases478, entry.hero = 238 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection478 : ∀ entry ∈ rowCases478, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase478 : ∀ entry ∈ rowCases478, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases479 : List PhysicalCase := [case432, case433]
theorem memberCase432 : case432 ∈ rowCases479 := by exact List.mem_cons_self
theorem memberCase433 : case433 ∈ rowCases479 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits479 : ∀ entry ∈ rowCases479, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case432_fitted, (List.forall_mem_cons.mpr ⟨case433_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked479 : ∀ entry ∈ rowCases479, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame432_checked, (List.forall_mem_cons.mpr ⟨frame433_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero479 : ∀ entry ∈ rowCases479, entry.hero = 238 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection479 : ∀ entry ∈ rowCases479, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase479 : ∀ entry ∈ rowCases479, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases480 : List PhysicalCase := [case434, case770]
theorem memberCase434 : case434 ∈ rowCases480 := by exact List.mem_cons_self
theorem memberCase770 : case770 ∈ rowCases480 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits480 : ∀ entry ∈ rowCases480, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case434_fitted, (List.forall_mem_cons.mpr ⟨case770_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked480 : ∀ entry ∈ rowCases480, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame434_checked, (List.forall_mem_cons.mpr ⟨frame770_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero480 : ∀ entry ∈ rowCases480, entry.hero = 239 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection480 : ∀ entry ∈ rowCases480, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase480 : ∀ entry ∈ rowCases480, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases481 : List PhysicalCase := [case435, case821]
theorem memberCase435 : case435 ∈ rowCases481 := by exact List.mem_cons_self
theorem memberCase821 : case821 ∈ rowCases481 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits481 : ∀ entry ∈ rowCases481, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case435_fitted, (List.forall_mem_cons.mpr ⟨case821_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked481 : ∀ entry ∈ rowCases481, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame435_checked, (List.forall_mem_cons.mpr ⟨frame821_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero481 : ∀ entry ∈ rowCases481, entry.hero = 239 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection481 : ∀ entry ∈ rowCases481, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase481 : ∀ entry ∈ rowCases481, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases482 : List PhysicalCase := []
theorem rowFits482 : ∀ entry ∈ rowCases482, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked482 : ∀ entry ∈ rowCases482, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero482 : ∀ entry ∈ rowCases482, entry.hero = 239 := by exact (by intro entry member; cases member)
theorem rowDirection482 : ∀ entry ∈ rowCases482, entry.direction = .east := by exact (by intro entry member; cases member)
theorem rowPhase482 : ∀ entry ∈ rowCases482, entry.phase = 5 := by exact (by intro entry member; cases member)
noncomputable def rowCases483 : List PhysicalCase := [case436, case799]
theorem memberCase436 : case436 ∈ rowCases483 := by exact List.mem_cons_self
theorem memberCase799 : case799 ∈ rowCases483 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits483 : ∀ entry ∈ rowCases483, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case436_fitted, (List.forall_mem_cons.mpr ⟨case799_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked483 : ∀ entry ∈ rowCases483, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame436_checked, (List.forall_mem_cons.mpr ⟨frame799_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero483 : ∀ entry ∈ rowCases483, entry.hero = 239 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection483 : ∀ entry ∈ rowCases483, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase483 : ∀ entry ∈ rowCases483, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases484 : List PhysicalCase := [case437]
theorem memberCase437 : case437 ∈ rowCases484 := by exact List.mem_cons_self
theorem rowFits484 : ∀ entry ∈ rowCases484, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case437_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked484 : ∀ entry ∈ rowCases484, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame437_checked, (by intro entry member; cases member)⟩)
theorem rowHero484 : ∀ entry ∈ rowCases484, entry.hero = 239 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection484 : ∀ entry ∈ rowCases484, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase484 : ∀ entry ∈ rowCases484, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases485 : List PhysicalCase := [case438, case439]
theorem memberCase438 : case438 ∈ rowCases485 := by exact List.mem_cons_self
theorem memberCase439 : case439 ∈ rowCases485 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits485 : ∀ entry ∈ rowCases485, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case438_fitted, (List.forall_mem_cons.mpr ⟨case439_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked485 : ∀ entry ∈ rowCases485, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame438_checked, (List.forall_mem_cons.mpr ⟨frame439_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero485 : ∀ entry ∈ rowCases485, entry.hero = 239 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection485 : ∀ entry ∈ rowCases485, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase485 : ∀ entry ∈ rowCases485, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases486 : List PhysicalCase := []
theorem rowFits486 : ∀ entry ∈ rowCases486, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked486 : ∀ entry ∈ rowCases486, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero486 : ∀ entry ∈ rowCases486, entry.hero = 239 := by exact (by intro entry member; cases member)
theorem rowDirection486 : ∀ entry ∈ rowCases486, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase486 : ∀ entry ∈ rowCases486, entry.phase = 5 := by exact (by intro entry member; cases member)
noncomputable def rowCases487 : List PhysicalCase := [case440, case441]
theorem memberCase440 : case440 ∈ rowCases487 := by exact List.mem_cons_self
theorem memberCase441 : case441 ∈ rowCases487 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits487 : ∀ entry ∈ rowCases487, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case440_fitted, (List.forall_mem_cons.mpr ⟨case441_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked487 : ∀ entry ∈ rowCases487, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame440_checked, (List.forall_mem_cons.mpr ⟨frame441_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero487 : ∀ entry ∈ rowCases487, entry.hero = 239 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection487 : ∀ entry ∈ rowCases487, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase487 : ∀ entry ∈ rowCases487, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases488 : List PhysicalCase := [case442, case776]
theorem memberCase442 : case442 ∈ rowCases488 := by exact List.mem_cons_self
theorem memberCase776 : case776 ∈ rowCases488 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits488 : ∀ entry ∈ rowCases488, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case442_fitted, (List.forall_mem_cons.mpr ⟨case776_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked488 : ∀ entry ∈ rowCases488, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame442_checked, (List.forall_mem_cons.mpr ⟨frame776_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero488 : ∀ entry ∈ rowCases488, entry.hero = 241 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection488 : ∀ entry ∈ rowCases488, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase488 : ∀ entry ∈ rowCases488, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases489 : List PhysicalCase := []
theorem rowFits489 : ∀ entry ∈ rowCases489, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked489 : ∀ entry ∈ rowCases489, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero489 : ∀ entry ∈ rowCases489, entry.hero = 241 := by exact (by intro entry member; cases member)
theorem rowDirection489 : ∀ entry ∈ rowCases489, entry.direction = .south := by exact (by intro entry member; cases member)
theorem rowPhase489 : ∀ entry ∈ rowCases489, entry.phase = 5 := by exact (by intro entry member; cases member)
noncomputable def rowCases490 : List PhysicalCase := [case443]
theorem memberCase443 : case443 ∈ rowCases490 := by exact List.mem_cons_self
theorem rowFits490 : ∀ entry ∈ rowCases490, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case443_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked490 : ∀ entry ∈ rowCases490, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame443_checked, (by intro entry member; cases member)⟩)
theorem rowHero490 : ∀ entry ∈ rowCases490, entry.hero = 241 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection490 : ∀ entry ∈ rowCases490, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase490 : ∀ entry ∈ rowCases490, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases491 : List PhysicalCase := []
theorem rowFits491 : ∀ entry ∈ rowCases491, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked491 : ∀ entry ∈ rowCases491, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero491 : ∀ entry ∈ rowCases491, entry.hero = 241 := by exact (by intro entry member; cases member)
theorem rowDirection491 : ∀ entry ∈ rowCases491, entry.direction = .west := by exact (by intro entry member; cases member)
theorem rowPhase491 : ∀ entry ∈ rowCases491, entry.phase = 5 := by exact (by intro entry member; cases member)
noncomputable def rowCases492 : List PhysicalCase := [case444, case445]
theorem memberCase444 : case444 ∈ rowCases492 := by exact List.mem_cons_self
theorem memberCase445 : case445 ∈ rowCases492 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits492 : ∀ entry ∈ rowCases492, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case444_fitted, (List.forall_mem_cons.mpr ⟨case445_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked492 : ∀ entry ∈ rowCases492, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame444_checked, (List.forall_mem_cons.mpr ⟨frame445_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero492 : ∀ entry ∈ rowCases492, entry.hero = 241 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection492 : ∀ entry ∈ rowCases492, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase492 : ∀ entry ∈ rowCases492, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases493 : List PhysicalCase := [case446]
theorem memberCase446 : case446 ∈ rowCases493 := by exact List.mem_cons_self
theorem rowFits493 : ∀ entry ∈ rowCases493, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case446_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked493 : ∀ entry ∈ rowCases493, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame446_checked, (by intro entry member; cases member)⟩)
theorem rowHero493 : ∀ entry ∈ rowCases493, entry.hero = 241 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection493 : ∀ entry ∈ rowCases493, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase493 : ∀ entry ∈ rowCases493, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases494 : List PhysicalCase := []
theorem rowFits494 : ∀ entry ∈ rowCases494, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked494 : ∀ entry ∈ rowCases494, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero494 : ∀ entry ∈ rowCases494, entry.hero = 241 := by exact (by intro entry member; cases member)
theorem rowDirection494 : ∀ entry ∈ rowCases494, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase494 : ∀ entry ∈ rowCases494, entry.phase = 5 := by exact (by intro entry member; cases member)
noncomputable def rowCases495 : List PhysicalCase := []
theorem rowFits495 : ∀ entry ∈ rowCases495, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked495 : ∀ entry ∈ rowCases495, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero495 : ∀ entry ∈ rowCases495, entry.hero = 241 := by exact (by intro entry member; cases member)
theorem rowDirection495 : ∀ entry ∈ rowCases495, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase495 : ∀ entry ∈ rowCases495, entry.phase = 5 := by exact (by intro entry member; cases member)
noncomputable def rowCases496 : List PhysicalCase := [case447, case780]
theorem memberCase447 : case447 ∈ rowCases496 := by exact List.mem_cons_self
theorem memberCase780 : case780 ∈ rowCases496 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits496 : ∀ entry ∈ rowCases496, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case447_fitted, (List.forall_mem_cons.mpr ⟨case780_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked496 : ∀ entry ∈ rowCases496, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame447_checked, (List.forall_mem_cons.mpr ⟨frame780_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero496 : ∀ entry ∈ rowCases496, entry.hero = 242 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection496 : ∀ entry ∈ rowCases496, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase496 : ∀ entry ∈ rowCases496, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases497 : List PhysicalCase := []
theorem rowFits497 : ∀ entry ∈ rowCases497, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked497 : ∀ entry ∈ rowCases497, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero497 : ∀ entry ∈ rowCases497, entry.hero = 242 := by exact (by intro entry member; cases member)
theorem rowDirection497 : ∀ entry ∈ rowCases497, entry.direction = .south := by exact (by intro entry member; cases member)
theorem rowPhase497 : ∀ entry ∈ rowCases497, entry.phase = 5 := by exact (by intro entry member; cases member)
noncomputable def rowCases498 : List PhysicalCase := []
theorem rowFits498 : ∀ entry ∈ rowCases498, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked498 : ∀ entry ∈ rowCases498, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero498 : ∀ entry ∈ rowCases498, entry.hero = 242 := by exact (by intro entry member; cases member)
theorem rowDirection498 : ∀ entry ∈ rowCases498, entry.direction = .east := by exact (by intro entry member; cases member)
theorem rowPhase498 : ∀ entry ∈ rowCases498, entry.phase = 5 := by exact (by intro entry member; cases member)
noncomputable def rowCases499 : List PhysicalCase := [case448]
theorem memberCase448 : case448 ∈ rowCases499 := by exact List.mem_cons_self
theorem rowFits499 : ∀ entry ∈ rowCases499, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case448_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked499 : ∀ entry ∈ rowCases499, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame448_checked, (by intro entry member; cases member)⟩)
theorem rowHero499 : ∀ entry ∈ rowCases499, entry.hero = 242 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection499 : ∀ entry ∈ rowCases499, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase499 : ∀ entry ∈ rowCases499, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
end NetHack.Soko12Forward220.Unified.P05
