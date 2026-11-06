import NetHack.Soko12Forward220.Unified.P00.OracleCases07
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P00
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
noncomputable def rowCases400 : List PhysicalCase := [case374, case744]
theorem memberCase374 : case374 ∈ rowCases400 := by exact List.mem_cons_self
theorem memberCase744 : case744 ∈ rowCases400 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits400 : ∀ entry ∈ rowCases400, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case374_fitted, (List.forall_mem_cons.mpr ⟨case744_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked400 : ∀ entry ∈ rowCases400, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame374_checked, (List.forall_mem_cons.mpr ⟨frame744_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero400 : ∀ entry ∈ rowCases400, entry.hero = 219 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection400 : ∀ entry ∈ rowCases400, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase400 : ∀ entry ∈ rowCases400, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases401 : List PhysicalCase := [case375, case795]
theorem memberCase375 : case375 ∈ rowCases401 := by exact List.mem_cons_self
theorem memberCase795 : case795 ∈ rowCases401 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits401 : ∀ entry ∈ rowCases401, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case375_fitted, (List.forall_mem_cons.mpr ⟨case795_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked401 : ∀ entry ∈ rowCases401, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame375_checked, (List.forall_mem_cons.mpr ⟨frame795_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero401 : ∀ entry ∈ rowCases401, entry.hero = 219 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection401 : ∀ entry ∈ rowCases401, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase401 : ∀ entry ∈ rowCases401, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases402 : List PhysicalCase := [case376]
theorem memberCase376 : case376 ∈ rowCases402 := by exact List.mem_cons_self
theorem rowFits402 : ∀ entry ∈ rowCases402, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case376_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked402 : ∀ entry ∈ rowCases402, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame376_checked, (by intro entry member; cases member)⟩)
theorem rowHero402 : ∀ entry ∈ rowCases402, entry.hero = 219 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection402 : ∀ entry ∈ rowCases402, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase402 : ∀ entry ∈ rowCases402, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases403 : List PhysicalCase := [case377]
theorem memberCase377 : case377 ∈ rowCases403 := by exact List.mem_cons_self
theorem rowFits403 : ∀ entry ∈ rowCases403, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case377_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked403 : ∀ entry ∈ rowCases403, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame377_checked, (by intro entry member; cases member)⟩)
theorem rowHero403 : ∀ entry ∈ rowCases403, entry.hero = 219 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection403 : ∀ entry ∈ rowCases403, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase403 : ∀ entry ∈ rowCases403, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases404 : List PhysicalCase := [case378, case379]
theorem memberCase378 : case378 ∈ rowCases404 := by exact List.mem_cons_self
theorem memberCase379 : case379 ∈ rowCases404 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits404 : ∀ entry ∈ rowCases404, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case378_fitted, (List.forall_mem_cons.mpr ⟨case379_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked404 : ∀ entry ∈ rowCases404, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame378_checked, (List.forall_mem_cons.mpr ⟨frame379_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero404 : ∀ entry ∈ rowCases404, entry.hero = 219 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection404 : ∀ entry ∈ rowCases404, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase404 : ∀ entry ∈ rowCases404, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases405 : List PhysicalCase := [case380, case381]
theorem memberCase380 : case380 ∈ rowCases405 := by exact List.mem_cons_self
theorem memberCase381 : case381 ∈ rowCases405 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits405 : ∀ entry ∈ rowCases405, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case380_fitted, (List.forall_mem_cons.mpr ⟨case381_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked405 : ∀ entry ∈ rowCases405, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame380_checked, (List.forall_mem_cons.mpr ⟨frame381_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero405 : ∀ entry ∈ rowCases405, entry.hero = 219 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection405 : ∀ entry ∈ rowCases405, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase405 : ∀ entry ∈ rowCases405, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases406 : List PhysicalCase := [case382, case383]
theorem memberCase382 : case382 ∈ rowCases406 := by exact List.mem_cons_self
theorem memberCase383 : case383 ∈ rowCases406 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits406 : ∀ entry ∈ rowCases406, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case382_fitted, (List.forall_mem_cons.mpr ⟨case383_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked406 : ∀ entry ∈ rowCases406, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame382_checked, (List.forall_mem_cons.mpr ⟨frame383_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero406 : ∀ entry ∈ rowCases406, entry.hero = 219 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection406 : ∀ entry ∈ rowCases406, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase406 : ∀ entry ∈ rowCases406, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases407 : List PhysicalCase := [case384, case385]
theorem memberCase384 : case384 ∈ rowCases407 := by exact List.mem_cons_self
theorem memberCase385 : case385 ∈ rowCases407 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits407 : ∀ entry ∈ rowCases407, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case384_fitted, (List.forall_mem_cons.mpr ⟨case385_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked407 : ∀ entry ∈ rowCases407, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame384_checked, (List.forall_mem_cons.mpr ⟨frame385_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero407 : ∀ entry ∈ rowCases407, entry.hero = 219 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection407 : ∀ entry ∈ rowCases407, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase407 : ∀ entry ∈ rowCases407, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases408 : List PhysicalCase := [case386, case748]
theorem memberCase386 : case386 ∈ rowCases408 := by exact List.mem_cons_self
theorem memberCase748 : case748 ∈ rowCases408 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits408 : ∀ entry ∈ rowCases408, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case386_fitted, (List.forall_mem_cons.mpr ⟨case748_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked408 : ∀ entry ∈ rowCases408, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame386_checked, (List.forall_mem_cons.mpr ⟨frame748_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero408 : ∀ entry ∈ rowCases408, entry.hero = 220 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection408 : ∀ entry ∈ rowCases408, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase408 : ∀ entry ∈ rowCases408, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases409 : List PhysicalCase := [case387, case799]
theorem memberCase387 : case387 ∈ rowCases409 := by exact List.mem_cons_self
theorem memberCase799 : case799 ∈ rowCases409 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits409 : ∀ entry ∈ rowCases409, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case387_fitted, (List.forall_mem_cons.mpr ⟨case799_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked409 : ∀ entry ∈ rowCases409, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame387_checked, (List.forall_mem_cons.mpr ⟨frame799_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero409 : ∀ entry ∈ rowCases409, entry.hero = 220 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection409 : ∀ entry ∈ rowCases409, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase409 : ∀ entry ∈ rowCases409, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases410 : List PhysicalCase := []
theorem rowFits410 : ∀ entry ∈ rowCases410, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked410 : ∀ entry ∈ rowCases410, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero410 : ∀ entry ∈ rowCases410, entry.hero = 220 := by exact (by intro entry member; cases member)
theorem rowDirection410 : ∀ entry ∈ rowCases410, entry.direction = .east := by exact (by intro entry member; cases member)
theorem rowPhase410 : ∀ entry ∈ rowCases410, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases411 : List PhysicalCase := [case388, case777]
theorem memberCase388 : case388 ∈ rowCases411 := by exact List.mem_cons_self
theorem memberCase777 : case777 ∈ rowCases411 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits411 : ∀ entry ∈ rowCases411, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case388_fitted, (List.forall_mem_cons.mpr ⟨case777_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked411 : ∀ entry ∈ rowCases411, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame388_checked, (List.forall_mem_cons.mpr ⟨frame777_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero411 : ∀ entry ∈ rowCases411, entry.hero = 220 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection411 : ∀ entry ∈ rowCases411, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase411 : ∀ entry ∈ rowCases411, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases412 : List PhysicalCase := []
theorem rowFits412 : ∀ entry ∈ rowCases412, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked412 : ∀ entry ∈ rowCases412, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero412 : ∀ entry ∈ rowCases412, entry.hero = 220 := by exact (by intro entry member; cases member)
theorem rowDirection412 : ∀ entry ∈ rowCases412, entry.direction = .northEast := by exact (by intro entry member; cases member)
theorem rowPhase412 : ∀ entry ∈ rowCases412, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases413 : List PhysicalCase := [case389, case390]
theorem memberCase389 : case389 ∈ rowCases413 := by exact List.mem_cons_self
theorem memberCase390 : case390 ∈ rowCases413 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits413 : ∀ entry ∈ rowCases413, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case389_fitted, (List.forall_mem_cons.mpr ⟨case390_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked413 : ∀ entry ∈ rowCases413, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame389_checked, (List.forall_mem_cons.mpr ⟨frame390_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero413 : ∀ entry ∈ rowCases413, entry.hero = 220 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection413 : ∀ entry ∈ rowCases413, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase413 : ∀ entry ∈ rowCases413, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases414 : List PhysicalCase := []
theorem rowFits414 : ∀ entry ∈ rowCases414, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked414 : ∀ entry ∈ rowCases414, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero414 : ∀ entry ∈ rowCases414, entry.hero = 220 := by exact (by intro entry member; cases member)
theorem rowDirection414 : ∀ entry ∈ rowCases414, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase414 : ∀ entry ∈ rowCases414, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases415 : List PhysicalCase := [case391, case392]
theorem memberCase391 : case391 ∈ rowCases415 := by exact List.mem_cons_self
theorem memberCase392 : case392 ∈ rowCases415 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits415 : ∀ entry ∈ rowCases415, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case391_fitted, (List.forall_mem_cons.mpr ⟨case392_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked415 : ∀ entry ∈ rowCases415, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame391_checked, (List.forall_mem_cons.mpr ⟨frame392_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero415 : ∀ entry ∈ rowCases415, entry.hero = 220 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection415 : ∀ entry ∈ rowCases415, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase415 : ∀ entry ∈ rowCases415, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases416 : List PhysicalCase := [case393, case750]
theorem memberCase393 : case393 ∈ rowCases416 := by exact List.mem_cons_self
theorem memberCase750 : case750 ∈ rowCases416 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits416 : ∀ entry ∈ rowCases416, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case393_fitted, (List.forall_mem_cons.mpr ⟨case750_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked416 : ∀ entry ∈ rowCases416, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame393_checked, (List.forall_mem_cons.mpr ⟨frame750_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero416 : ∀ entry ∈ rowCases416, entry.hero = 236 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection416 : ∀ entry ∈ rowCases416, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase416 : ∀ entry ∈ rowCases416, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases417 : List PhysicalCase := [case394, case801]
theorem memberCase394 : case394 ∈ rowCases417 := by exact List.mem_cons_self
theorem memberCase801 : case801 ∈ rowCases417 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits417 : ∀ entry ∈ rowCases417, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case394_fitted, (List.forall_mem_cons.mpr ⟨case801_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked417 : ∀ entry ∈ rowCases417, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame394_checked, (List.forall_mem_cons.mpr ⟨frame801_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero417 : ∀ entry ∈ rowCases417, entry.hero = 236 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection417 : ∀ entry ∈ rowCases417, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase417 : ∀ entry ∈ rowCases417, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases418 : List PhysicalCase := [case395, case784]
theorem memberCase395 : case395 ∈ rowCases418 := by exact List.mem_cons_self
theorem memberCase784 : case784 ∈ rowCases418 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits418 : ∀ entry ∈ rowCases418, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case395_fitted, (List.forall_mem_cons.mpr ⟨case784_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked418 : ∀ entry ∈ rowCases418, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame395_checked, (List.forall_mem_cons.mpr ⟨frame784_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero418 : ∀ entry ∈ rowCases418, entry.hero = 236 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection418 : ∀ entry ∈ rowCases418, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase418 : ∀ entry ∈ rowCases418, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases419 : List PhysicalCase := []
theorem rowFits419 : ∀ entry ∈ rowCases419, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked419 : ∀ entry ∈ rowCases419, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero419 : ∀ entry ∈ rowCases419, entry.hero = 236 := by exact (by intro entry member; cases member)
theorem rowDirection419 : ∀ entry ∈ rowCases419, entry.direction = .west := by exact (by intro entry member; cases member)
theorem rowPhase419 : ∀ entry ∈ rowCases419, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases420 : List PhysicalCase := [case396, case397]
theorem memberCase396 : case396 ∈ rowCases420 := by exact List.mem_cons_self
theorem memberCase397 : case397 ∈ rowCases420 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits420 : ∀ entry ∈ rowCases420, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case396_fitted, (List.forall_mem_cons.mpr ⟨case397_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked420 : ∀ entry ∈ rowCases420, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame396_checked, (List.forall_mem_cons.mpr ⟨frame397_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero420 : ∀ entry ∈ rowCases420, entry.hero = 236 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection420 : ∀ entry ∈ rowCases420, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase420 : ∀ entry ∈ rowCases420, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases421 : List PhysicalCase := []
theorem rowFits421 : ∀ entry ∈ rowCases421, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked421 : ∀ entry ∈ rowCases421, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero421 : ∀ entry ∈ rowCases421, entry.hero = 236 := by exact (by intro entry member; cases member)
theorem rowDirection421 : ∀ entry ∈ rowCases421, entry.direction = .northWest := by exact (by intro entry member; cases member)
theorem rowPhase421 : ∀ entry ∈ rowCases421, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases422 : List PhysicalCase := [case398, case399]
theorem memberCase398 : case398 ∈ rowCases422 := by exact List.mem_cons_self
theorem memberCase399 : case399 ∈ rowCases422 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits422 : ∀ entry ∈ rowCases422, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case398_fitted, (List.forall_mem_cons.mpr ⟨case399_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked422 : ∀ entry ∈ rowCases422, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame398_checked, (List.forall_mem_cons.mpr ⟨frame399_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero422 : ∀ entry ∈ rowCases422, entry.hero = 236 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection422 : ∀ entry ∈ rowCases422, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase422 : ∀ entry ∈ rowCases422, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases423 : List PhysicalCase := []
theorem rowFits423 : ∀ entry ∈ rowCases423, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked423 : ∀ entry ∈ rowCases423, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero423 : ∀ entry ∈ rowCases423, entry.hero = 236 := by exact (by intro entry member; cases member)
theorem rowDirection423 : ∀ entry ∈ rowCases423, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase423 : ∀ entry ∈ rowCases423, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases424 : List PhysicalCase := [case400, case752]
theorem memberCase400 : case400 ∈ rowCases424 := by exact List.mem_cons_self
theorem memberCase752 : case752 ∈ rowCases424 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits424 : ∀ entry ∈ rowCases424, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case400_fitted, (List.forall_mem_cons.mpr ⟨case752_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked424 : ∀ entry ∈ rowCases424, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame400_checked, (List.forall_mem_cons.mpr ⟨frame752_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero424 : ∀ entry ∈ rowCases424, entry.hero = 237 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection424 : ∀ entry ∈ rowCases424, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase424 : ∀ entry ∈ rowCases424, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases425 : List PhysicalCase := [case401, case803]
theorem memberCase401 : case401 ∈ rowCases425 := by exact List.mem_cons_self
theorem memberCase803 : case803 ∈ rowCases425 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits425 : ∀ entry ∈ rowCases425, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case401_fitted, (List.forall_mem_cons.mpr ⟨case803_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked425 : ∀ entry ∈ rowCases425, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame401_checked, (List.forall_mem_cons.mpr ⟨frame803_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero425 : ∀ entry ∈ rowCases425, entry.hero = 237 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection425 : ∀ entry ∈ rowCases425, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase425 : ∀ entry ∈ rowCases425, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases426 : List PhysicalCase := [case402, case788]
theorem memberCase402 : case402 ∈ rowCases426 := by exact List.mem_cons_self
theorem memberCase788 : case788 ∈ rowCases426 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits426 : ∀ entry ∈ rowCases426, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case402_fitted, (List.forall_mem_cons.mpr ⟨case788_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked426 : ∀ entry ∈ rowCases426, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame402_checked, (List.forall_mem_cons.mpr ⟨frame788_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero426 : ∀ entry ∈ rowCases426, entry.hero = 237 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection426 : ∀ entry ∈ rowCases426, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase426 : ∀ entry ∈ rowCases426, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases427 : List PhysicalCase := [case403]
theorem memberCase403 : case403 ∈ rowCases427 := by exact List.mem_cons_self
theorem rowFits427 : ∀ entry ∈ rowCases427, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case403_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked427 : ∀ entry ∈ rowCases427, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame403_checked, (by intro entry member; cases member)⟩)
theorem rowHero427 : ∀ entry ∈ rowCases427, entry.hero = 237 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection427 : ∀ entry ∈ rowCases427, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase427 : ∀ entry ∈ rowCases427, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases428 : List PhysicalCase := [case404, case405]
theorem memberCase404 : case404 ∈ rowCases428 := by exact List.mem_cons_self
theorem memberCase405 : case405 ∈ rowCases428 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits428 : ∀ entry ∈ rowCases428, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case404_fitted, (List.forall_mem_cons.mpr ⟨case405_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked428 : ∀ entry ∈ rowCases428, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame404_checked, (List.forall_mem_cons.mpr ⟨frame405_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero428 : ∀ entry ∈ rowCases428, entry.hero = 237 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection428 : ∀ entry ∈ rowCases428, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase428 : ∀ entry ∈ rowCases428, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases429 : List PhysicalCase := [case406, case407]
theorem memberCase406 : case406 ∈ rowCases429 := by exact List.mem_cons_self
theorem memberCase407 : case407 ∈ rowCases429 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits429 : ∀ entry ∈ rowCases429, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case406_fitted, (List.forall_mem_cons.mpr ⟨case407_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked429 : ∀ entry ∈ rowCases429, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame406_checked, (List.forall_mem_cons.mpr ⟨frame407_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero429 : ∀ entry ∈ rowCases429, entry.hero = 237 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection429 : ∀ entry ∈ rowCases429, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase429 : ∀ entry ∈ rowCases429, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases430 : List PhysicalCase := [case408, case409]
theorem memberCase408 : case408 ∈ rowCases430 := by exact List.mem_cons_self
theorem memberCase409 : case409 ∈ rowCases430 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits430 : ∀ entry ∈ rowCases430, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case408_fitted, (List.forall_mem_cons.mpr ⟨case409_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked430 : ∀ entry ∈ rowCases430, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame408_checked, (List.forall_mem_cons.mpr ⟨frame409_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero430 : ∀ entry ∈ rowCases430, entry.hero = 237 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection430 : ∀ entry ∈ rowCases430, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase430 : ∀ entry ∈ rowCases430, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases431 : List PhysicalCase := [case410, case411]
theorem memberCase410 : case410 ∈ rowCases431 := by exact List.mem_cons_self
theorem memberCase411 : case411 ∈ rowCases431 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits431 : ∀ entry ∈ rowCases431, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case410_fitted, (List.forall_mem_cons.mpr ⟨case411_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked431 : ∀ entry ∈ rowCases431, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame410_checked, (List.forall_mem_cons.mpr ⟨frame411_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero431 : ∀ entry ∈ rowCases431, entry.hero = 237 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection431 : ∀ entry ∈ rowCases431, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase431 : ∀ entry ∈ rowCases431, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases432 : List PhysicalCase := [case412, case756]
theorem memberCase412 : case412 ∈ rowCases432 := by exact List.mem_cons_self
theorem memberCase756 : case756 ∈ rowCases432 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits432 : ∀ entry ∈ rowCases432, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case412_fitted, (List.forall_mem_cons.mpr ⟨case756_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked432 : ∀ entry ∈ rowCases432, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame412_checked, (List.forall_mem_cons.mpr ⟨frame756_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero432 : ∀ entry ∈ rowCases432, entry.hero = 238 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection432 : ∀ entry ∈ rowCases432, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase432 : ∀ entry ∈ rowCases432, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases433 : List PhysicalCase := [case413, case807]
theorem memberCase413 : case413 ∈ rowCases433 := by exact List.mem_cons_self
theorem memberCase807 : case807 ∈ rowCases433 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits433 : ∀ entry ∈ rowCases433, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case413_fitted, (List.forall_mem_cons.mpr ⟨case807_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked433 : ∀ entry ∈ rowCases433, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame413_checked, (List.forall_mem_cons.mpr ⟨frame807_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero433 : ∀ entry ∈ rowCases433, entry.hero = 238 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection433 : ∀ entry ∈ rowCases433, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase433 : ∀ entry ∈ rowCases433, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases434 : List PhysicalCase := [case414]
theorem memberCase414 : case414 ∈ rowCases434 := by exact List.mem_cons_self
theorem rowFits434 : ∀ entry ∈ rowCases434, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case414_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked434 : ∀ entry ∈ rowCases434, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame414_checked, (by intro entry member; cases member)⟩)
theorem rowHero434 : ∀ entry ∈ rowCases434, entry.hero = 238 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection434 : ∀ entry ∈ rowCases434, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase434 : ∀ entry ∈ rowCases434, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases435 : List PhysicalCase := [case415, case785]
theorem memberCase415 : case415 ∈ rowCases435 := by exact List.mem_cons_self
theorem memberCase785 : case785 ∈ rowCases435 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits435 : ∀ entry ∈ rowCases435, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case415_fitted, (List.forall_mem_cons.mpr ⟨case785_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked435 : ∀ entry ∈ rowCases435, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame415_checked, (List.forall_mem_cons.mpr ⟨frame785_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero435 : ∀ entry ∈ rowCases435, entry.hero = 238 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection435 : ∀ entry ∈ rowCases435, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase435 : ∀ entry ∈ rowCases435, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases436 : List PhysicalCase := [case416, case417]
theorem memberCase416 : case416 ∈ rowCases436 := by exact List.mem_cons_self
theorem memberCase417 : case417 ∈ rowCases436 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits436 : ∀ entry ∈ rowCases436, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case416_fitted, (List.forall_mem_cons.mpr ⟨case417_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked436 : ∀ entry ∈ rowCases436, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame416_checked, (List.forall_mem_cons.mpr ⟨frame417_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero436 : ∀ entry ∈ rowCases436, entry.hero = 238 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection436 : ∀ entry ∈ rowCases436, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase436 : ∀ entry ∈ rowCases436, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases437 : List PhysicalCase := [case418, case419]
theorem memberCase418 : case418 ∈ rowCases437 := by exact List.mem_cons_self
theorem memberCase419 : case419 ∈ rowCases437 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits437 : ∀ entry ∈ rowCases437, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case418_fitted, (List.forall_mem_cons.mpr ⟨case419_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked437 : ∀ entry ∈ rowCases437, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame418_checked, (List.forall_mem_cons.mpr ⟨frame419_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero437 : ∀ entry ∈ rowCases437, entry.hero = 238 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection437 : ∀ entry ∈ rowCases437, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase437 : ∀ entry ∈ rowCases437, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases438 : List PhysicalCase := [case420, case421]
theorem memberCase420 : case420 ∈ rowCases438 := by exact List.mem_cons_self
theorem memberCase421 : case421 ∈ rowCases438 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits438 : ∀ entry ∈ rowCases438, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case420_fitted, (List.forall_mem_cons.mpr ⟨case421_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked438 : ∀ entry ∈ rowCases438, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame420_checked, (List.forall_mem_cons.mpr ⟨frame421_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero438 : ∀ entry ∈ rowCases438, entry.hero = 238 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection438 : ∀ entry ∈ rowCases438, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase438 : ∀ entry ∈ rowCases438, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases439 : List PhysicalCase := [case422, case423]
theorem memberCase422 : case422 ∈ rowCases439 := by exact List.mem_cons_self
theorem memberCase423 : case423 ∈ rowCases439 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits439 : ∀ entry ∈ rowCases439, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case422_fitted, (List.forall_mem_cons.mpr ⟨case423_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked439 : ∀ entry ∈ rowCases439, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame422_checked, (List.forall_mem_cons.mpr ⟨frame423_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero439 : ∀ entry ∈ rowCases439, entry.hero = 238 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection439 : ∀ entry ∈ rowCases439, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase439 : ∀ entry ∈ rowCases439, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases440 : List PhysicalCase := [case424, case760]
theorem memberCase424 : case424 ∈ rowCases440 := by exact List.mem_cons_self
theorem memberCase760 : case760 ∈ rowCases440 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits440 : ∀ entry ∈ rowCases440, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case424_fitted, (List.forall_mem_cons.mpr ⟨case760_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked440 : ∀ entry ∈ rowCases440, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame424_checked, (List.forall_mem_cons.mpr ⟨frame760_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero440 : ∀ entry ∈ rowCases440, entry.hero = 239 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection440 : ∀ entry ∈ rowCases440, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase440 : ∀ entry ∈ rowCases440, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases441 : List PhysicalCase := [case425, case811]
theorem memberCase425 : case425 ∈ rowCases441 := by exact List.mem_cons_self
theorem memberCase811 : case811 ∈ rowCases441 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits441 : ∀ entry ∈ rowCases441, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case425_fitted, (List.forall_mem_cons.mpr ⟨case811_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked441 : ∀ entry ∈ rowCases441, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame425_checked, (List.forall_mem_cons.mpr ⟨frame811_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero441 : ∀ entry ∈ rowCases441, entry.hero = 239 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection441 : ∀ entry ∈ rowCases441, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase441 : ∀ entry ∈ rowCases441, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases442 : List PhysicalCase := []
theorem rowFits442 : ∀ entry ∈ rowCases442, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked442 : ∀ entry ∈ rowCases442, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero442 : ∀ entry ∈ rowCases442, entry.hero = 239 := by exact (by intro entry member; cases member)
theorem rowDirection442 : ∀ entry ∈ rowCases442, entry.direction = .east := by exact (by intro entry member; cases member)
theorem rowPhase442 : ∀ entry ∈ rowCases442, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases443 : List PhysicalCase := [case426, case789]
theorem memberCase426 : case426 ∈ rowCases443 := by exact List.mem_cons_self
theorem memberCase789 : case789 ∈ rowCases443 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits443 : ∀ entry ∈ rowCases443, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case426_fitted, (List.forall_mem_cons.mpr ⟨case789_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked443 : ∀ entry ∈ rowCases443, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame426_checked, (List.forall_mem_cons.mpr ⟨frame789_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero443 : ∀ entry ∈ rowCases443, entry.hero = 239 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection443 : ∀ entry ∈ rowCases443, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase443 : ∀ entry ∈ rowCases443, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases444 : List PhysicalCase := [case427]
theorem memberCase427 : case427 ∈ rowCases444 := by exact List.mem_cons_self
theorem rowFits444 : ∀ entry ∈ rowCases444, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case427_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked444 : ∀ entry ∈ rowCases444, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame427_checked, (by intro entry member; cases member)⟩)
theorem rowHero444 : ∀ entry ∈ rowCases444, entry.hero = 239 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection444 : ∀ entry ∈ rowCases444, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase444 : ∀ entry ∈ rowCases444, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases445 : List PhysicalCase := [case428, case429]
theorem memberCase428 : case428 ∈ rowCases445 := by exact List.mem_cons_self
theorem memberCase429 : case429 ∈ rowCases445 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits445 : ∀ entry ∈ rowCases445, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case428_fitted, (List.forall_mem_cons.mpr ⟨case429_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked445 : ∀ entry ∈ rowCases445, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame428_checked, (List.forall_mem_cons.mpr ⟨frame429_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero445 : ∀ entry ∈ rowCases445, entry.hero = 239 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection445 : ∀ entry ∈ rowCases445, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase445 : ∀ entry ∈ rowCases445, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases446 : List PhysicalCase := []
theorem rowFits446 : ∀ entry ∈ rowCases446, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked446 : ∀ entry ∈ rowCases446, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero446 : ∀ entry ∈ rowCases446, entry.hero = 239 := by exact (by intro entry member; cases member)
theorem rowDirection446 : ∀ entry ∈ rowCases446, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase446 : ∀ entry ∈ rowCases446, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases447 : List PhysicalCase := [case430, case431]
theorem memberCase430 : case430 ∈ rowCases447 := by exact List.mem_cons_self
theorem memberCase431 : case431 ∈ rowCases447 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits447 : ∀ entry ∈ rowCases447, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case430_fitted, (List.forall_mem_cons.mpr ⟨case431_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked447 : ∀ entry ∈ rowCases447, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame430_checked, (List.forall_mem_cons.mpr ⟨frame431_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero447 : ∀ entry ∈ rowCases447, entry.hero = 239 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection447 : ∀ entry ∈ rowCases447, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase447 : ∀ entry ∈ rowCases447, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases448 : List PhysicalCase := [case432, case766]
theorem memberCase432 : case432 ∈ rowCases448 := by exact List.mem_cons_self
theorem memberCase766 : case766 ∈ rowCases448 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits448 : ∀ entry ∈ rowCases448, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case432_fitted, (List.forall_mem_cons.mpr ⟨case766_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked448 : ∀ entry ∈ rowCases448, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame432_checked, (List.forall_mem_cons.mpr ⟨frame766_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero448 : ∀ entry ∈ rowCases448, entry.hero = 241 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection448 : ∀ entry ∈ rowCases448, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase448 : ∀ entry ∈ rowCases448, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases449 : List PhysicalCase := []
theorem rowFits449 : ∀ entry ∈ rowCases449, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked449 : ∀ entry ∈ rowCases449, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero449 : ∀ entry ∈ rowCases449, entry.hero = 241 := by exact (by intro entry member; cases member)
theorem rowDirection449 : ∀ entry ∈ rowCases449, entry.direction = .south := by exact (by intro entry member; cases member)
theorem rowPhase449 : ∀ entry ∈ rowCases449, entry.phase = 0 := by exact (by intro entry member; cases member)
end NetHack.Soko12Forward220.Unified.P00
