import NetHack.Soko12Forward220.Unified.P01.OracleCases06
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P01
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
noncomputable def rowCases350 : List PhysicalCase := [case312, case313]
theorem memberCase312 : case312 ∈ rowCases350 := by exact List.mem_cons_self
theorem memberCase313 : case313 ∈ rowCases350 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits350 : ∀ entry ∈ rowCases350, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case312_fitted, (List.forall_mem_cons.mpr ⟨case313_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked350 : ∀ entry ∈ rowCases350, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame312_checked, (List.forall_mem_cons.mpr ⟨frame313_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero350 : ∀ entry ∈ rowCases350, entry.hero = 210 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection350 : ∀ entry ∈ rowCases350, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase350 : ∀ entry ∈ rowCases350, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases351 : List PhysicalCase := []
theorem rowFits351 : ∀ entry ∈ rowCases351, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked351 : ∀ entry ∈ rowCases351, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero351 : ∀ entry ∈ rowCases351, entry.hero = 210 := by exact (by intro entry member; cases member)
theorem rowDirection351 : ∀ entry ∈ rowCases351, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase351 : ∀ entry ∈ rowCases351, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases352 : List PhysicalCase := [case314, case724]
theorem memberCase314 : case314 ∈ rowCases352 := by exact List.mem_cons_self
theorem memberCase724 : case724 ∈ rowCases352 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits352 : ∀ entry ∈ rowCases352, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case314_fitted, (List.forall_mem_cons.mpr ⟨case724_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked352 : ∀ entry ∈ rowCases352, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame314_checked, (List.forall_mem_cons.mpr ⟨frame724_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero352 : ∀ entry ∈ rowCases352, entry.hero = 211 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection352 : ∀ entry ∈ rowCases352, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase352 : ∀ entry ∈ rowCases352, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases353 : List PhysicalCase := [case315, case785]
theorem memberCase315 : case315 ∈ rowCases353 := by exact List.mem_cons_self
theorem memberCase785 : case785 ∈ rowCases353 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits353 : ∀ entry ∈ rowCases353, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case315_fitted, (List.forall_mem_cons.mpr ⟨case785_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked353 : ∀ entry ∈ rowCases353, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame315_checked, (List.forall_mem_cons.mpr ⟨frame785_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero353 : ∀ entry ∈ rowCases353, entry.hero = 211 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection353 : ∀ entry ∈ rowCases353, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase353 : ∀ entry ∈ rowCases353, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases354 : List PhysicalCase := [case316, case760]
theorem memberCase316 : case316 ∈ rowCases354 := by exact List.mem_cons_self
theorem memberCase760 : case760 ∈ rowCases354 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits354 : ∀ entry ∈ rowCases354, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case316_fitted, (List.forall_mem_cons.mpr ⟨case760_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked354 : ∀ entry ∈ rowCases354, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame316_checked, (List.forall_mem_cons.mpr ⟨frame760_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero354 : ∀ entry ∈ rowCases354, entry.hero = 211 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection354 : ∀ entry ∈ rowCases354, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase354 : ∀ entry ∈ rowCases354, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases355 : List PhysicalCase := [case317]
theorem memberCase317 : case317 ∈ rowCases355 := by exact List.mem_cons_self
theorem rowFits355 : ∀ entry ∈ rowCases355, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case317_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked355 : ∀ entry ∈ rowCases355, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame317_checked, (by intro entry member; cases member)⟩)
theorem rowHero355 : ∀ entry ∈ rowCases355, entry.hero = 211 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection355 : ∀ entry ∈ rowCases355, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase355 : ∀ entry ∈ rowCases355, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases356 : List PhysicalCase := [case318, case319]
theorem memberCase318 : case318 ∈ rowCases356 := by exact List.mem_cons_self
theorem memberCase319 : case319 ∈ rowCases356 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits356 : ∀ entry ∈ rowCases356, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case318_fitted, (List.forall_mem_cons.mpr ⟨case319_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked356 : ∀ entry ∈ rowCases356, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame318_checked, (List.forall_mem_cons.mpr ⟨frame319_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero356 : ∀ entry ∈ rowCases356, entry.hero = 211 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection356 : ∀ entry ∈ rowCases356, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase356 : ∀ entry ∈ rowCases356, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases357 : List PhysicalCase := [case320, case321]
theorem memberCase320 : case320 ∈ rowCases357 := by exact List.mem_cons_self
theorem memberCase321 : case321 ∈ rowCases357 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits357 : ∀ entry ∈ rowCases357, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case320_fitted, (List.forall_mem_cons.mpr ⟨case321_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked357 : ∀ entry ∈ rowCases357, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame320_checked, (List.forall_mem_cons.mpr ⟨frame321_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero357 : ∀ entry ∈ rowCases357, entry.hero = 211 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection357 : ∀ entry ∈ rowCases357, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase357 : ∀ entry ∈ rowCases357, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases358 : List PhysicalCase := [case322, case323]
theorem memberCase322 : case322 ∈ rowCases358 := by exact List.mem_cons_self
theorem memberCase323 : case323 ∈ rowCases358 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits358 : ∀ entry ∈ rowCases358, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case322_fitted, (List.forall_mem_cons.mpr ⟨case323_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked358 : ∀ entry ∈ rowCases358, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame322_checked, (List.forall_mem_cons.mpr ⟨frame323_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero358 : ∀ entry ∈ rowCases358, entry.hero = 211 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection358 : ∀ entry ∈ rowCases358, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase358 : ∀ entry ∈ rowCases358, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases359 : List PhysicalCase := [case324, case325]
theorem memberCase324 : case324 ∈ rowCases359 := by exact List.mem_cons_self
theorem memberCase325 : case325 ∈ rowCases359 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits359 : ∀ entry ∈ rowCases359, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case324_fitted, (List.forall_mem_cons.mpr ⟨case325_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked359 : ∀ entry ∈ rowCases359, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame324_checked, (List.forall_mem_cons.mpr ⟨frame325_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero359 : ∀ entry ∈ rowCases359, entry.hero = 211 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection359 : ∀ entry ∈ rowCases359, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase359 : ∀ entry ∈ rowCases359, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases360 : List PhysicalCase := [case326, case728]
theorem memberCase326 : case326 ∈ rowCases360 := by exact List.mem_cons_self
theorem memberCase728 : case728 ∈ rowCases360 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits360 : ∀ entry ∈ rowCases360, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case326_fitted, (List.forall_mem_cons.mpr ⟨case728_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked360 : ∀ entry ∈ rowCases360, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame326_checked, (List.forall_mem_cons.mpr ⟨frame728_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero360 : ∀ entry ∈ rowCases360, entry.hero = 212 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection360 : ∀ entry ∈ rowCases360, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase360 : ∀ entry ∈ rowCases360, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases361 : List PhysicalCase := [case327, case789]
theorem memberCase327 : case327 ∈ rowCases361 := by exact List.mem_cons_self
theorem memberCase789 : case789 ∈ rowCases361 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits361 : ∀ entry ∈ rowCases361, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case327_fitted, (List.forall_mem_cons.mpr ⟨case789_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked361 : ∀ entry ∈ rowCases361, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame327_checked, (List.forall_mem_cons.mpr ⟨frame789_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero361 : ∀ entry ∈ rowCases361, entry.hero = 212 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection361 : ∀ entry ∈ rowCases361, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase361 : ∀ entry ∈ rowCases361, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases362 : List PhysicalCase := [case328, case764]
theorem memberCase328 : case328 ∈ rowCases362 := by exact List.mem_cons_self
theorem memberCase764 : case764 ∈ rowCases362 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits362 : ∀ entry ∈ rowCases362, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case328_fitted, (List.forall_mem_cons.mpr ⟨case764_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked362 : ∀ entry ∈ rowCases362, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame328_checked, (List.forall_mem_cons.mpr ⟨frame764_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero362 : ∀ entry ∈ rowCases362, entry.hero = 212 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection362 : ∀ entry ∈ rowCases362, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase362 : ∀ entry ∈ rowCases362, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases363 : List PhysicalCase := [case329, case757]
theorem memberCase329 : case329 ∈ rowCases363 := by exact List.mem_cons_self
theorem memberCase757 : case757 ∈ rowCases363 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits363 : ∀ entry ∈ rowCases363, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case329_fitted, (List.forall_mem_cons.mpr ⟨case757_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked363 : ∀ entry ∈ rowCases363, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame329_checked, (List.forall_mem_cons.mpr ⟨frame757_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero363 : ∀ entry ∈ rowCases363, entry.hero = 212 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection363 : ∀ entry ∈ rowCases363, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase363 : ∀ entry ∈ rowCases363, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases364 : List PhysicalCase := [case330, case331]
theorem memberCase330 : case330 ∈ rowCases364 := by exact List.mem_cons_self
theorem memberCase331 : case331 ∈ rowCases364 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits364 : ∀ entry ∈ rowCases364, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case330_fitted, (List.forall_mem_cons.mpr ⟨case331_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked364 : ∀ entry ∈ rowCases364, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame330_checked, (List.forall_mem_cons.mpr ⟨frame331_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero364 : ∀ entry ∈ rowCases364, entry.hero = 212 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection364 : ∀ entry ∈ rowCases364, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase364 : ∀ entry ∈ rowCases364, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases365 : List PhysicalCase := [case332, case333]
theorem memberCase332 : case332 ∈ rowCases365 := by exact List.mem_cons_self
theorem memberCase333 : case333 ∈ rowCases365 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits365 : ∀ entry ∈ rowCases365, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case332_fitted, (List.forall_mem_cons.mpr ⟨case333_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked365 : ∀ entry ∈ rowCases365, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame332_checked, (List.forall_mem_cons.mpr ⟨frame333_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero365 : ∀ entry ∈ rowCases365, entry.hero = 212 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection365 : ∀ entry ∈ rowCases365, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase365 : ∀ entry ∈ rowCases365, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases366 : List PhysicalCase := [case334, case335]
theorem memberCase334 : case334 ∈ rowCases366 := by exact List.mem_cons_self
theorem memberCase335 : case335 ∈ rowCases366 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits366 : ∀ entry ∈ rowCases366, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case334_fitted, (List.forall_mem_cons.mpr ⟨case335_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked366 : ∀ entry ∈ rowCases366, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame334_checked, (List.forall_mem_cons.mpr ⟨frame335_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero366 : ∀ entry ∈ rowCases366, entry.hero = 212 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection366 : ∀ entry ∈ rowCases366, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase366 : ∀ entry ∈ rowCases366, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases367 : List PhysicalCase := [case336, case337]
theorem memberCase336 : case336 ∈ rowCases367 := by exact List.mem_cons_self
theorem memberCase337 : case337 ∈ rowCases367 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits367 : ∀ entry ∈ rowCases367, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case336_fitted, (List.forall_mem_cons.mpr ⟨case337_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked367 : ∀ entry ∈ rowCases367, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame336_checked, (List.forall_mem_cons.mpr ⟨frame337_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero367 : ∀ entry ∈ rowCases367, entry.hero = 212 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection367 : ∀ entry ∈ rowCases367, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase367 : ∀ entry ∈ rowCases367, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases368 : List PhysicalCase := [case338, case732]
theorem memberCase338 : case338 ∈ rowCases368 := by exact List.mem_cons_self
theorem memberCase732 : case732 ∈ rowCases368 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits368 : ∀ entry ∈ rowCases368, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case338_fitted, (List.forall_mem_cons.mpr ⟨case732_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked368 : ∀ entry ∈ rowCases368, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame338_checked, (List.forall_mem_cons.mpr ⟨frame732_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero368 : ∀ entry ∈ rowCases368, entry.hero = 213 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection368 : ∀ entry ∈ rowCases368, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase368 : ∀ entry ∈ rowCases368, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases369 : List PhysicalCase := [case339, case793]
theorem memberCase339 : case339 ∈ rowCases369 := by exact List.mem_cons_self
theorem memberCase793 : case793 ∈ rowCases369 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits369 : ∀ entry ∈ rowCases369, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case339_fitted, (List.forall_mem_cons.mpr ⟨case793_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked369 : ∀ entry ∈ rowCases369, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame339_checked, (List.forall_mem_cons.mpr ⟨frame793_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero369 : ∀ entry ∈ rowCases369, entry.hero = 213 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection369 : ∀ entry ∈ rowCases369, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase369 : ∀ entry ∈ rowCases369, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases370 : List PhysicalCase := [case340, case766]
theorem memberCase340 : case340 ∈ rowCases370 := by exact List.mem_cons_self
theorem memberCase766 : case766 ∈ rowCases370 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits370 : ∀ entry ∈ rowCases370, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case340_fitted, (List.forall_mem_cons.mpr ⟨case766_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked370 : ∀ entry ∈ rowCases370, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame340_checked, (List.forall_mem_cons.mpr ⟨frame766_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero370 : ∀ entry ∈ rowCases370, entry.hero = 213 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection370 : ∀ entry ∈ rowCases370, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase370 : ∀ entry ∈ rowCases370, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases371 : List PhysicalCase := [case341, case761]
theorem memberCase341 : case341 ∈ rowCases371 := by exact List.mem_cons_self
theorem memberCase761 : case761 ∈ rowCases371 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits371 : ∀ entry ∈ rowCases371, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case341_fitted, (List.forall_mem_cons.mpr ⟨case761_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked371 : ∀ entry ∈ rowCases371, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame341_checked, (List.forall_mem_cons.mpr ⟨frame761_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero371 : ∀ entry ∈ rowCases371, entry.hero = 213 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection371 : ∀ entry ∈ rowCases371, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase371 : ∀ entry ∈ rowCases371, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases372 : List PhysicalCase := []
theorem rowFits372 : ∀ entry ∈ rowCases372, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked372 : ∀ entry ∈ rowCases372, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero372 : ∀ entry ∈ rowCases372, entry.hero = 213 := by exact (by intro entry member; cases member)
theorem rowDirection372 : ∀ entry ∈ rowCases372, entry.direction = .northEast := by exact (by intro entry member; cases member)
theorem rowPhase372 : ∀ entry ∈ rowCases372, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases373 : List PhysicalCase := [case342, case343]
theorem memberCase342 : case342 ∈ rowCases373 := by exact List.mem_cons_self
theorem memberCase343 : case343 ∈ rowCases373 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits373 : ∀ entry ∈ rowCases373, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case342_fitted, (List.forall_mem_cons.mpr ⟨case343_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked373 : ∀ entry ∈ rowCases373, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame342_checked, (List.forall_mem_cons.mpr ⟨frame343_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero373 : ∀ entry ∈ rowCases373, entry.hero = 213 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection373 : ∀ entry ∈ rowCases373, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase373 : ∀ entry ∈ rowCases373, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases374 : List PhysicalCase := []
theorem rowFits374 : ∀ entry ∈ rowCases374, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked374 : ∀ entry ∈ rowCases374, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero374 : ∀ entry ∈ rowCases374, entry.hero = 213 := by exact (by intro entry member; cases member)
theorem rowDirection374 : ∀ entry ∈ rowCases374, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase374 : ∀ entry ∈ rowCases374, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases375 : List PhysicalCase := [case344, case345]
theorem memberCase344 : case344 ∈ rowCases375 := by exact List.mem_cons_self
theorem memberCase345 : case345 ∈ rowCases375 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits375 : ∀ entry ∈ rowCases375, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case344_fitted, (List.forall_mem_cons.mpr ⟨case345_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked375 : ∀ entry ∈ rowCases375, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame344_checked, (List.forall_mem_cons.mpr ⟨frame345_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero375 : ∀ entry ∈ rowCases375, entry.hero = 213 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection375 : ∀ entry ∈ rowCases375, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase375 : ∀ entry ∈ rowCases375, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases376 : List PhysicalCase := []
theorem rowFits376 : ∀ entry ∈ rowCases376, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked376 : ∀ entry ∈ rowCases376, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero376 : ∀ entry ∈ rowCases376, entry.hero = 214 := by exact (by intro entry member; cases member)
theorem rowDirection376 : ∀ entry ∈ rowCases376, entry.direction = .north := by exact (by intro entry member; cases member)
theorem rowPhase376 : ∀ entry ∈ rowCases376, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases377 : List PhysicalCase := []
theorem rowFits377 : ∀ entry ∈ rowCases377, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked377 : ∀ entry ∈ rowCases377, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero377 : ∀ entry ∈ rowCases377, entry.hero = 214 := by exact (by intro entry member; cases member)
theorem rowDirection377 : ∀ entry ∈ rowCases377, entry.direction = .south := by exact (by intro entry member; cases member)
theorem rowPhase377 : ∀ entry ∈ rowCases377, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases378 : List PhysicalCase := [case346, case770]
theorem memberCase346 : case346 ∈ rowCases378 := by exact List.mem_cons_self
theorem memberCase770 : case770 ∈ rowCases378 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits378 : ∀ entry ∈ rowCases378, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case346_fitted, (List.forall_mem_cons.mpr ⟨case770_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked378 : ∀ entry ∈ rowCases378, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame346_checked, (List.forall_mem_cons.mpr ⟨frame770_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero378 : ∀ entry ∈ rowCases378, entry.hero = 214 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection378 : ∀ entry ∈ rowCases378, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase378 : ∀ entry ∈ rowCases378, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases379 : List PhysicalCase := [case347, case765]
theorem memberCase347 : case347 ∈ rowCases379 := by exact List.mem_cons_self
theorem memberCase765 : case765 ∈ rowCases379 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits379 : ∀ entry ∈ rowCases379, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case347_fitted, (List.forall_mem_cons.mpr ⟨case765_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked379 : ∀ entry ∈ rowCases379, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame347_checked, (List.forall_mem_cons.mpr ⟨frame765_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero379 : ∀ entry ∈ rowCases379, entry.hero = 214 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection379 : ∀ entry ∈ rowCases379, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase379 : ∀ entry ∈ rowCases379, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases380 : List PhysicalCase := [case348]
theorem memberCase348 : case348 ∈ rowCases380 := by exact List.mem_cons_self
theorem rowFits380 : ∀ entry ∈ rowCases380, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case348_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked380 : ∀ entry ∈ rowCases380, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame348_checked, (by intro entry member; cases member)⟩)
theorem rowHero380 : ∀ entry ∈ rowCases380, entry.hero = 214 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection380 : ∀ entry ∈ rowCases380, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase380 : ∀ entry ∈ rowCases380, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases381 : List PhysicalCase := [case349]
theorem memberCase349 : case349 ∈ rowCases381 := by exact List.mem_cons_self
theorem rowFits381 : ∀ entry ∈ rowCases381, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case349_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked381 : ∀ entry ∈ rowCases381, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame349_checked, (by intro entry member; cases member)⟩)
theorem rowHero381 : ∀ entry ∈ rowCases381, entry.hero = 214 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection381 : ∀ entry ∈ rowCases381, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase381 : ∀ entry ∈ rowCases381, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases382 : List PhysicalCase := [case350]
theorem memberCase350 : case350 ∈ rowCases382 := by exact List.mem_cons_self
theorem rowFits382 : ∀ entry ∈ rowCases382, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case350_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked382 : ∀ entry ∈ rowCases382, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame350_checked, (by intro entry member; cases member)⟩)
theorem rowHero382 : ∀ entry ∈ rowCases382, entry.hero = 214 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection382 : ∀ entry ∈ rowCases382, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase382 : ∀ entry ∈ rowCases382, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases383 : List PhysicalCase := [case351]
theorem memberCase351 : case351 ∈ rowCases383 := by exact List.mem_cons_self
theorem rowFits383 : ∀ entry ∈ rowCases383, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case351_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked383 : ∀ entry ∈ rowCases383, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame351_checked, (by intro entry member; cases member)⟩)
theorem rowHero383 : ∀ entry ∈ rowCases383, entry.hero = 214 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection383 : ∀ entry ∈ rowCases383, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase383 : ∀ entry ∈ rowCases383, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases384 : List PhysicalCase := [case352, case734]
theorem memberCase352 : case352 ∈ rowCases384 := by exact List.mem_cons_self
theorem memberCase734 : case734 ∈ rowCases384 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits384 : ∀ entry ∈ rowCases384, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case352_fitted, (List.forall_mem_cons.mpr ⟨case734_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked384 : ∀ entry ∈ rowCases384, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame352_checked, (List.forall_mem_cons.mpr ⟨frame734_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero384 : ∀ entry ∈ rowCases384, entry.hero = 215 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection384 : ∀ entry ∈ rowCases384, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase384 : ∀ entry ∈ rowCases384, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases385 : List PhysicalCase := [case353]
theorem memberCase353 : case353 ∈ rowCases385 := by exact List.mem_cons_self
theorem rowFits385 : ∀ entry ∈ rowCases385, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case353_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked385 : ∀ entry ∈ rowCases385, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame353_checked, (by intro entry member; cases member)⟩)
theorem rowHero385 : ∀ entry ∈ rowCases385, entry.hero = 215 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection385 : ∀ entry ∈ rowCases385, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase385 : ∀ entry ∈ rowCases385, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases386 : List PhysicalCase := [case354]
theorem memberCase354 : case354 ∈ rowCases386 := by exact List.mem_cons_self
theorem rowFits386 : ∀ entry ∈ rowCases386, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case354_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked386 : ∀ entry ∈ rowCases386, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame354_checked, (by intro entry member; cases member)⟩)
theorem rowHero386 : ∀ entry ∈ rowCases386, entry.hero = 215 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection386 : ∀ entry ∈ rowCases386, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase386 : ∀ entry ∈ rowCases386, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases387 : List PhysicalCase := [case355, case767]
theorem memberCase355 : case355 ∈ rowCases387 := by exact List.mem_cons_self
theorem memberCase767 : case767 ∈ rowCases387 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits387 : ∀ entry ∈ rowCases387, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case355_fitted, (List.forall_mem_cons.mpr ⟨case767_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked387 : ∀ entry ∈ rowCases387, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame355_checked, (List.forall_mem_cons.mpr ⟨frame767_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero387 : ∀ entry ∈ rowCases387, entry.hero = 215 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection387 : ∀ entry ∈ rowCases387, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase387 : ∀ entry ∈ rowCases387, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases388 : List PhysicalCase := [case356, case357]
theorem memberCase356 : case356 ∈ rowCases388 := by exact List.mem_cons_self
theorem memberCase357 : case357 ∈ rowCases388 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits388 : ∀ entry ∈ rowCases388, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case356_fitted, (List.forall_mem_cons.mpr ⟨case357_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked388 : ∀ entry ∈ rowCases388, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame356_checked, (List.forall_mem_cons.mpr ⟨frame357_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero388 : ∀ entry ∈ rowCases388, entry.hero = 215 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection388 : ∀ entry ∈ rowCases388, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase388 : ∀ entry ∈ rowCases388, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases389 : List PhysicalCase := []
theorem rowFits389 : ∀ entry ∈ rowCases389, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked389 : ∀ entry ∈ rowCases389, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero389 : ∀ entry ∈ rowCases389, entry.hero = 215 := by exact (by intro entry member; cases member)
theorem rowDirection389 : ∀ entry ∈ rowCases389, entry.direction = .northWest := by exact (by intro entry member; cases member)
theorem rowPhase389 : ∀ entry ∈ rowCases389, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases390 : List PhysicalCase := [case358, case359]
theorem memberCase358 : case358 ∈ rowCases390 := by exact List.mem_cons_self
theorem memberCase359 : case359 ∈ rowCases390 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits390 : ∀ entry ∈ rowCases390, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case358_fitted, (List.forall_mem_cons.mpr ⟨case359_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked390 : ∀ entry ∈ rowCases390, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame358_checked, (List.forall_mem_cons.mpr ⟨frame359_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero390 : ∀ entry ∈ rowCases390, entry.hero = 215 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection390 : ∀ entry ∈ rowCases390, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase390 : ∀ entry ∈ rowCases390, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases391 : List PhysicalCase := []
theorem rowFits391 : ∀ entry ∈ rowCases391, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked391 : ∀ entry ∈ rowCases391, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero391 : ∀ entry ∈ rowCases391, entry.hero = 215 := by exact (by intro entry member; cases member)
theorem rowDirection391 : ∀ entry ∈ rowCases391, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase391 : ∀ entry ∈ rowCases391, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases392 : List PhysicalCase := [case360, case736]
theorem memberCase360 : case360 ∈ rowCases392 := by exact List.mem_cons_self
theorem memberCase736 : case736 ∈ rowCases392 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits392 : ∀ entry ∈ rowCases392, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case360_fitted, (List.forall_mem_cons.mpr ⟨case736_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked392 : ∀ entry ∈ rowCases392, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame360_checked, (List.forall_mem_cons.mpr ⟨frame736_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero392 : ∀ entry ∈ rowCases392, entry.hero = 216 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection392 : ∀ entry ∈ rowCases392, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase392 : ∀ entry ∈ rowCases392, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases393 : List PhysicalCase := [case361]
theorem memberCase361 : case361 ∈ rowCases393 := by exact List.mem_cons_self
theorem rowFits393 : ∀ entry ∈ rowCases393, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case361_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked393 : ∀ entry ∈ rowCases393, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame361_checked, (by intro entry member; cases member)⟩)
theorem rowHero393 : ∀ entry ∈ rowCases393, entry.hero = 216 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection393 : ∀ entry ∈ rowCases393, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase393 : ∀ entry ∈ rowCases393, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases394 : List PhysicalCase := []
theorem rowFits394 : ∀ entry ∈ rowCases394, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked394 : ∀ entry ∈ rowCases394, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero394 : ∀ entry ∈ rowCases394, entry.hero = 216 := by exact (by intro entry member; cases member)
theorem rowDirection394 : ∀ entry ∈ rowCases394, entry.direction = .east := by exact (by intro entry member; cases member)
theorem rowPhase394 : ∀ entry ∈ rowCases394, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases395 : List PhysicalCase := [case362, case771]
theorem memberCase362 : case362 ∈ rowCases395 := by exact List.mem_cons_self
theorem memberCase771 : case771 ∈ rowCases395 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits395 : ∀ entry ∈ rowCases395, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case362_fitted, (List.forall_mem_cons.mpr ⟨case771_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked395 : ∀ entry ∈ rowCases395, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame362_checked, (List.forall_mem_cons.mpr ⟨frame771_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero395 : ∀ entry ∈ rowCases395, entry.hero = 216 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection395 : ∀ entry ∈ rowCases395, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase395 : ∀ entry ∈ rowCases395, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases396 : List PhysicalCase := [case363]
theorem memberCase363 : case363 ∈ rowCases396 := by exact List.mem_cons_self
theorem rowFits396 : ∀ entry ∈ rowCases396, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case363_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked396 : ∀ entry ∈ rowCases396, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame363_checked, (by intro entry member; cases member)⟩)
theorem rowHero396 : ∀ entry ∈ rowCases396, entry.hero = 216 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection396 : ∀ entry ∈ rowCases396, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase396 : ∀ entry ∈ rowCases396, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases397 : List PhysicalCase := [case364, case365]
theorem memberCase364 : case364 ∈ rowCases397 := by exact List.mem_cons_self
theorem memberCase365 : case365 ∈ rowCases397 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits397 : ∀ entry ∈ rowCases397, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case364_fitted, (List.forall_mem_cons.mpr ⟨case365_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked397 : ∀ entry ∈ rowCases397, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame364_checked, (List.forall_mem_cons.mpr ⟨frame365_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero397 : ∀ entry ∈ rowCases397, entry.hero = 216 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection397 : ∀ entry ∈ rowCases397, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase397 : ∀ entry ∈ rowCases397, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases398 : List PhysicalCase := []
theorem rowFits398 : ∀ entry ∈ rowCases398, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked398 : ∀ entry ∈ rowCases398, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero398 : ∀ entry ∈ rowCases398, entry.hero = 216 := by exact (by intro entry member; cases member)
theorem rowDirection398 : ∀ entry ∈ rowCases398, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase398 : ∀ entry ∈ rowCases398, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases399 : List PhysicalCase := [case366, case367]
theorem memberCase366 : case366 ∈ rowCases399 := by exact List.mem_cons_self
theorem memberCase367 : case367 ∈ rowCases399 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits399 : ∀ entry ∈ rowCases399, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case366_fitted, (List.forall_mem_cons.mpr ⟨case367_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked399 : ∀ entry ∈ rowCases399, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame366_checked, (List.forall_mem_cons.mpr ⟨frame367_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero399 : ∀ entry ∈ rowCases399, entry.hero = 216 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection399 : ∀ entry ∈ rowCases399, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase399 : ∀ entry ∈ rowCases399, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
end NetHack.Soko12Forward220.Unified.P01
