import NetHack.Soko12Forward220.Unified.P04.OracleCases05
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P04
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
noncomputable def rowCases300 : List PhysicalCase := [case235, case236]
theorem memberCase235 : case235 ∈ rowCases300 := by exact List.mem_cons_self
theorem memberCase236 : case236 ∈ rowCases300 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits300 : ∀ entry ∈ rowCases300, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case235_fitted, (List.forall_mem_cons.mpr ⟨case236_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked300 : ∀ entry ∈ rowCases300, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame235_checked, (List.forall_mem_cons.mpr ⟨frame236_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero300 : ∀ entry ∈ rowCases300, entry.hero = 185 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection300 : ∀ entry ∈ rowCases300, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase300 : ∀ entry ∈ rowCases300, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases301 : List PhysicalCase := [case237, case238]
theorem memberCase237 : case237 ∈ rowCases301 := by exact List.mem_cons_self
theorem memberCase238 : case238 ∈ rowCases301 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits301 : ∀ entry ∈ rowCases301, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case237_fitted, (List.forall_mem_cons.mpr ⟨case238_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked301 : ∀ entry ∈ rowCases301, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame237_checked, (List.forall_mem_cons.mpr ⟨frame238_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero301 : ∀ entry ∈ rowCases301, entry.hero = 185 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection301 : ∀ entry ∈ rowCases301, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase301 : ∀ entry ∈ rowCases301, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases302 : List PhysicalCase := [case239, case240]
theorem memberCase239 : case239 ∈ rowCases302 := by exact List.mem_cons_self
theorem memberCase240 : case240 ∈ rowCases302 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits302 : ∀ entry ∈ rowCases302, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case239_fitted, (List.forall_mem_cons.mpr ⟨case240_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked302 : ∀ entry ∈ rowCases302, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame239_checked, (List.forall_mem_cons.mpr ⟨frame240_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero302 : ∀ entry ∈ rowCases302, entry.hero = 185 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection302 : ∀ entry ∈ rowCases302, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase302 : ∀ entry ∈ rowCases302, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases303 : List PhysicalCase := [case241, case242]
theorem memberCase241 : case241 ∈ rowCases303 := by exact List.mem_cons_self
theorem memberCase242 : case242 ∈ rowCases303 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits303 : ∀ entry ∈ rowCases303, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case241_fitted, (List.forall_mem_cons.mpr ⟨case242_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked303 : ∀ entry ∈ rowCases303, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame241_checked, (List.forall_mem_cons.mpr ⟨frame242_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero303 : ∀ entry ∈ rowCases303, entry.hero = 185 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection303 : ∀ entry ∈ rowCases303, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase303 : ∀ entry ∈ rowCases303, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases304 : List PhysicalCase := [case243, case712]
theorem memberCase243 : case243 ∈ rowCases304 := by exact List.mem_cons_self
theorem memberCase712 : case712 ∈ rowCases304 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits304 : ∀ entry ∈ rowCases304, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case243_fitted, (List.forall_mem_cons.mpr ⟨case712_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked304 : ∀ entry ∈ rowCases304, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame243_checked, (List.forall_mem_cons.mpr ⟨frame712_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero304 : ∀ entry ∈ rowCases304, entry.hero = 186 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection304 : ∀ entry ∈ rowCases304, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase304 : ∀ entry ∈ rowCases304, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases305 : List PhysicalCase := [case244, case765]
theorem memberCase244 : case244 ∈ rowCases305 := by exact List.mem_cons_self
theorem memberCase765 : case765 ∈ rowCases305 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits305 : ∀ entry ∈ rowCases305, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case244_fitted, (List.forall_mem_cons.mpr ⟨case765_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked305 : ∀ entry ∈ rowCases305, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame244_checked, (List.forall_mem_cons.mpr ⟨frame765_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero305 : ∀ entry ∈ rowCases305, entry.hero = 186 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection305 : ∀ entry ∈ rowCases305, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase305 : ∀ entry ∈ rowCases305, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases306 : List PhysicalCase := [case245]
theorem memberCase245 : case245 ∈ rowCases306 := by exact List.mem_cons_self
theorem rowFits306 : ∀ entry ∈ rowCases306, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case245_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked306 : ∀ entry ∈ rowCases306, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame245_checked, (by intro entry member; cases member)⟩)
theorem rowHero306 : ∀ entry ∈ rowCases306, entry.hero = 186 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection306 : ∀ entry ∈ rowCases306, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase306 : ∀ entry ∈ rowCases306, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases307 : List PhysicalCase := [case246, case733]
theorem memberCase246 : case246 ∈ rowCases307 := by exact List.mem_cons_self
theorem memberCase733 : case733 ∈ rowCases307 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits307 : ∀ entry ∈ rowCases307, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case246_fitted, (List.forall_mem_cons.mpr ⟨case733_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked307 : ∀ entry ∈ rowCases307, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame246_checked, (List.forall_mem_cons.mpr ⟨frame733_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero307 : ∀ entry ∈ rowCases307, entry.hero = 186 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection307 : ∀ entry ∈ rowCases307, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase307 : ∀ entry ∈ rowCases307, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases308 : List PhysicalCase := [case247, case248]
theorem memberCase247 : case247 ∈ rowCases308 := by exact List.mem_cons_self
theorem memberCase248 : case248 ∈ rowCases308 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits308 : ∀ entry ∈ rowCases308, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case247_fitted, (List.forall_mem_cons.mpr ⟨case248_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked308 : ∀ entry ∈ rowCases308, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame247_checked, (List.forall_mem_cons.mpr ⟨frame248_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero308 : ∀ entry ∈ rowCases308, entry.hero = 186 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection308 : ∀ entry ∈ rowCases308, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase308 : ∀ entry ∈ rowCases308, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases309 : List PhysicalCase := [case249, case250]
theorem memberCase249 : case249 ∈ rowCases309 := by exact List.mem_cons_self
theorem memberCase250 : case250 ∈ rowCases309 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits309 : ∀ entry ∈ rowCases309, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case249_fitted, (List.forall_mem_cons.mpr ⟨case250_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked309 : ∀ entry ∈ rowCases309, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame249_checked, (List.forall_mem_cons.mpr ⟨frame250_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero309 : ∀ entry ∈ rowCases309, entry.hero = 186 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection309 : ∀ entry ∈ rowCases309, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase309 : ∀ entry ∈ rowCases309, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases310 : List PhysicalCase := [case251, case252]
theorem memberCase251 : case251 ∈ rowCases310 := by exact List.mem_cons_self
theorem memberCase252 : case252 ∈ rowCases310 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits310 : ∀ entry ∈ rowCases310, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case251_fitted, (List.forall_mem_cons.mpr ⟨case252_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked310 : ∀ entry ∈ rowCases310, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame251_checked, (List.forall_mem_cons.mpr ⟨frame252_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero310 : ∀ entry ∈ rowCases310, entry.hero = 186 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection310 : ∀ entry ∈ rowCases310, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase310 : ∀ entry ∈ rowCases310, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases311 : List PhysicalCase := [case253, case254]
theorem memberCase253 : case253 ∈ rowCases311 := by exact List.mem_cons_self
theorem memberCase254 : case254 ∈ rowCases311 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits311 : ∀ entry ∈ rowCases311, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case253_fitted, (List.forall_mem_cons.mpr ⟨case254_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked311 : ∀ entry ∈ rowCases311, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame253_checked, (List.forall_mem_cons.mpr ⟨frame254_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero311 : ∀ entry ∈ rowCases311, entry.hero = 186 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection311 : ∀ entry ∈ rowCases311, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase311 : ∀ entry ∈ rowCases311, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases312 : List PhysicalCase := [case255, case716]
theorem memberCase255 : case255 ∈ rowCases312 := by exact List.mem_cons_self
theorem memberCase716 : case716 ∈ rowCases312 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits312 : ∀ entry ∈ rowCases312, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case255_fitted, (List.forall_mem_cons.mpr ⟨case716_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked312 : ∀ entry ∈ rowCases312, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame255_checked, (List.forall_mem_cons.mpr ⟨frame716_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero312 : ∀ entry ∈ rowCases312, entry.hero = 187 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection312 : ∀ entry ∈ rowCases312, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase312 : ∀ entry ∈ rowCases312, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases313 : List PhysicalCase := [case256, case769]
theorem memberCase256 : case256 ∈ rowCases313 := by exact List.mem_cons_self
theorem memberCase769 : case769 ∈ rowCases313 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits313 : ∀ entry ∈ rowCases313, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case256_fitted, (List.forall_mem_cons.mpr ⟨case769_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked313 : ∀ entry ∈ rowCases313, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame256_checked, (List.forall_mem_cons.mpr ⟨frame769_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero313 : ∀ entry ∈ rowCases313, entry.hero = 187 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection313 : ∀ entry ∈ rowCases313, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase313 : ∀ entry ∈ rowCases313, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases314 : List PhysicalCase := []
theorem rowFits314 : ∀ entry ∈ rowCases314, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked314 : ∀ entry ∈ rowCases314, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero314 : ∀ entry ∈ rowCases314, entry.hero = 187 := by exact (by intro entry member; cases member)
theorem rowDirection314 : ∀ entry ∈ rowCases314, entry.direction = .east := by exact (by intro entry member; cases member)
theorem rowPhase314 : ∀ entry ∈ rowCases314, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases315 : List PhysicalCase := [case257, case737]
theorem memberCase257 : case257 ∈ rowCases315 := by exact List.mem_cons_self
theorem memberCase737 : case737 ∈ rowCases315 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits315 : ∀ entry ∈ rowCases315, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case257_fitted, (List.forall_mem_cons.mpr ⟨case737_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked315 : ∀ entry ∈ rowCases315, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame257_checked, (List.forall_mem_cons.mpr ⟨frame737_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero315 : ∀ entry ∈ rowCases315, entry.hero = 187 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection315 : ∀ entry ∈ rowCases315, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase315 : ∀ entry ∈ rowCases315, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases316 : List PhysicalCase := []
theorem rowFits316 : ∀ entry ∈ rowCases316, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked316 : ∀ entry ∈ rowCases316, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero316 : ∀ entry ∈ rowCases316, entry.hero = 187 := by exact (by intro entry member; cases member)
theorem rowDirection316 : ∀ entry ∈ rowCases316, entry.direction = .northEast := by exact (by intro entry member; cases member)
theorem rowPhase316 : ∀ entry ∈ rowCases316, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases317 : List PhysicalCase := [case258, case259]
theorem memberCase258 : case258 ∈ rowCases317 := by exact List.mem_cons_self
theorem memberCase259 : case259 ∈ rowCases317 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits317 : ∀ entry ∈ rowCases317, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case258_fitted, (List.forall_mem_cons.mpr ⟨case259_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked317 : ∀ entry ∈ rowCases317, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame258_checked, (List.forall_mem_cons.mpr ⟨frame259_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero317 : ∀ entry ∈ rowCases317, entry.hero = 187 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection317 : ∀ entry ∈ rowCases317, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase317 : ∀ entry ∈ rowCases317, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases318 : List PhysicalCase := [case260]
theorem memberCase260 : case260 ∈ rowCases318 := by exact List.mem_cons_self
theorem rowFits318 : ∀ entry ∈ rowCases318, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case260_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked318 : ∀ entry ∈ rowCases318, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame260_checked, (by intro entry member; cases member)⟩)
theorem rowHero318 : ∀ entry ∈ rowCases318, entry.hero = 187 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection318 : ∀ entry ∈ rowCases318, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase318 : ∀ entry ∈ rowCases318, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases319 : List PhysicalCase := [case261, case262]
theorem memberCase261 : case261 ∈ rowCases319 := by exact List.mem_cons_self
theorem memberCase262 : case262 ∈ rowCases319 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits319 : ∀ entry ∈ rowCases319, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case261_fitted, (List.forall_mem_cons.mpr ⟨case262_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked319 : ∀ entry ∈ rowCases319, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame261_checked, (List.forall_mem_cons.mpr ⟨frame262_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero319 : ∀ entry ∈ rowCases319, entry.hero = 187 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection319 : ∀ entry ∈ rowCases319, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase319 : ∀ entry ∈ rowCases319, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases320 : List PhysicalCase := [case263]
theorem memberCase263 : case263 ∈ rowCases320 := by exact List.mem_cons_self
theorem rowFits320 : ∀ entry ∈ rowCases320, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case263_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked320 : ∀ entry ∈ rowCases320, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame263_checked, (by intro entry member; cases member)⟩)
theorem rowHero320 : ∀ entry ∈ rowCases320, entry.hero = 189 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection320 : ∀ entry ∈ rowCases320, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase320 : ∀ entry ∈ rowCases320, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases321 : List PhysicalCase := [case264, case775]
theorem memberCase264 : case264 ∈ rowCases321 := by exact List.mem_cons_self
theorem memberCase775 : case775 ∈ rowCases321 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits321 : ∀ entry ∈ rowCases321, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case264_fitted, (List.forall_mem_cons.mpr ⟨case775_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked321 : ∀ entry ∈ rowCases321, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame264_checked, (List.forall_mem_cons.mpr ⟨frame775_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero321 : ∀ entry ∈ rowCases321, entry.hero = 189 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection321 : ∀ entry ∈ rowCases321, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase321 : ∀ entry ∈ rowCases321, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases322 : List PhysicalCase := [case265, case744]
theorem memberCase265 : case265 ∈ rowCases322 := by exact List.mem_cons_self
theorem memberCase744 : case744 ∈ rowCases322 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits322 : ∀ entry ∈ rowCases322, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case265_fitted, (List.forall_mem_cons.mpr ⟨case744_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked322 : ∀ entry ∈ rowCases322, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame265_checked, (List.forall_mem_cons.mpr ⟨frame744_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero322 : ∀ entry ∈ rowCases322, entry.hero = 189 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection322 : ∀ entry ∈ rowCases322, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase322 : ∀ entry ∈ rowCases322, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases323 : List PhysicalCase := []
theorem rowFits323 : ∀ entry ∈ rowCases323, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked323 : ∀ entry ∈ rowCases323, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero323 : ∀ entry ∈ rowCases323, entry.hero = 189 := by exact (by intro entry member; cases member)
theorem rowDirection323 : ∀ entry ∈ rowCases323, entry.direction = .west := by exact (by intro entry member; cases member)
theorem rowPhase323 : ∀ entry ∈ rowCases323, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases324 : List PhysicalCase := [case266, case267]
theorem memberCase266 : case266 ∈ rowCases324 := by exact List.mem_cons_self
theorem memberCase267 : case267 ∈ rowCases324 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits324 : ∀ entry ∈ rowCases324, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case266_fitted, (List.forall_mem_cons.mpr ⟨case267_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked324 : ∀ entry ∈ rowCases324, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame266_checked, (List.forall_mem_cons.mpr ⟨frame267_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero324 : ∀ entry ∈ rowCases324, entry.hero = 189 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection324 : ∀ entry ∈ rowCases324, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase324 : ∀ entry ∈ rowCases324, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases325 : List PhysicalCase := []
theorem rowFits325 : ∀ entry ∈ rowCases325, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked325 : ∀ entry ∈ rowCases325, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero325 : ∀ entry ∈ rowCases325, entry.hero = 189 := by exact (by intro entry member; cases member)
theorem rowDirection325 : ∀ entry ∈ rowCases325, entry.direction = .northWest := by exact (by intro entry member; cases member)
theorem rowPhase325 : ∀ entry ∈ rowCases325, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases326 : List PhysicalCase := [case268, case269]
theorem memberCase268 : case268 ∈ rowCases326 := by exact List.mem_cons_self
theorem memberCase269 : case269 ∈ rowCases326 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits326 : ∀ entry ∈ rowCases326, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case268_fitted, (List.forall_mem_cons.mpr ⟨case269_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked326 : ∀ entry ∈ rowCases326, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame268_checked, (List.forall_mem_cons.mpr ⟨frame269_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero326 : ∀ entry ∈ rowCases326, entry.hero = 189 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection326 : ∀ entry ∈ rowCases326, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase326 : ∀ entry ∈ rowCases326, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases327 : List PhysicalCase := [case270]
theorem memberCase270 : case270 ∈ rowCases327 := by exact List.mem_cons_self
theorem rowFits327 : ∀ entry ∈ rowCases327, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case270_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked327 : ∀ entry ∈ rowCases327, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame270_checked, (by intro entry member; cases member)⟩)
theorem rowHero327 : ∀ entry ∈ rowCases327, entry.hero = 189 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection327 : ∀ entry ∈ rowCases327, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase327 : ∀ entry ∈ rowCases327, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases328 : List PhysicalCase := [case271]
theorem memberCase271 : case271 ∈ rowCases328 := by exact List.mem_cons_self
theorem rowFits328 : ∀ entry ∈ rowCases328, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case271_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked328 : ∀ entry ∈ rowCases328, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame271_checked, (by intro entry member; cases member)⟩)
theorem rowHero328 : ∀ entry ∈ rowCases328, entry.hero = 190 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection328 : ∀ entry ∈ rowCases328, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase328 : ∀ entry ∈ rowCases328, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases329 : List PhysicalCase := [case272, case779]
theorem memberCase272 : case272 ∈ rowCases329 := by exact List.mem_cons_self
theorem memberCase779 : case779 ∈ rowCases329 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits329 : ∀ entry ∈ rowCases329, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case272_fitted, (List.forall_mem_cons.mpr ⟨case779_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked329 : ∀ entry ∈ rowCases329, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame272_checked, (List.forall_mem_cons.mpr ⟨frame779_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero329 : ∀ entry ∈ rowCases329, entry.hero = 190 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection329 : ∀ entry ∈ rowCases329, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase329 : ∀ entry ∈ rowCases329, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases330 : List PhysicalCase := [case273, case746]
theorem memberCase273 : case273 ∈ rowCases330 := by exact List.mem_cons_self
theorem memberCase746 : case746 ∈ rowCases330 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits330 : ∀ entry ∈ rowCases330, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case273_fitted, (List.forall_mem_cons.mpr ⟨case746_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked330 : ∀ entry ∈ rowCases330, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame273_checked, (List.forall_mem_cons.mpr ⟨frame746_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero330 : ∀ entry ∈ rowCases330, entry.hero = 190 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection330 : ∀ entry ∈ rowCases330, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase330 : ∀ entry ∈ rowCases330, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases331 : List PhysicalCase := [case274]
theorem memberCase274 : case274 ∈ rowCases331 := by exact List.mem_cons_self
theorem rowFits331 : ∀ entry ∈ rowCases331, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case274_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked331 : ∀ entry ∈ rowCases331, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame274_checked, (by intro entry member; cases member)⟩)
theorem rowHero331 : ∀ entry ∈ rowCases331, entry.hero = 190 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection331 : ∀ entry ∈ rowCases331, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase331 : ∀ entry ∈ rowCases331, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases332 : List PhysicalCase := []
theorem rowFits332 : ∀ entry ∈ rowCases332, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked332 : ∀ entry ∈ rowCases332, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero332 : ∀ entry ∈ rowCases332, entry.hero = 190 := by exact (by intro entry member; cases member)
theorem rowDirection332 : ∀ entry ∈ rowCases332, entry.direction = .northEast := by exact (by intro entry member; cases member)
theorem rowPhase332 : ∀ entry ∈ rowCases332, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases333 : List PhysicalCase := [case275, case276]
theorem memberCase275 : case275 ∈ rowCases333 := by exact List.mem_cons_self
theorem memberCase276 : case276 ∈ rowCases333 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits333 : ∀ entry ∈ rowCases333, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case275_fitted, (List.forall_mem_cons.mpr ⟨case276_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked333 : ∀ entry ∈ rowCases333, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame275_checked, (List.forall_mem_cons.mpr ⟨frame276_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero333 : ∀ entry ∈ rowCases333, entry.hero = 190 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection333 : ∀ entry ∈ rowCases333, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase333 : ∀ entry ∈ rowCases333, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases334 : List PhysicalCase := []
theorem rowFits334 : ∀ entry ∈ rowCases334, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked334 : ∀ entry ∈ rowCases334, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero334 : ∀ entry ∈ rowCases334, entry.hero = 190 := by exact (by intro entry member; cases member)
theorem rowDirection334 : ∀ entry ∈ rowCases334, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase334 : ∀ entry ∈ rowCases334, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases335 : List PhysicalCase := [case277, case278]
theorem memberCase277 : case277 ∈ rowCases335 := by exact List.mem_cons_self
theorem memberCase278 : case278 ∈ rowCases335 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits335 : ∀ entry ∈ rowCases335, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case277_fitted, (List.forall_mem_cons.mpr ⟨case278_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked335 : ∀ entry ∈ rowCases335, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame277_checked, (List.forall_mem_cons.mpr ⟨frame278_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero335 : ∀ entry ∈ rowCases335, entry.hero = 190 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection335 : ∀ entry ∈ rowCases335, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase335 : ∀ entry ∈ rowCases335, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases336 : List PhysicalCase := []
theorem rowFits336 : ∀ entry ∈ rowCases336, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked336 : ∀ entry ∈ rowCases336, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero336 : ∀ entry ∈ rowCases336, entry.hero = 191 := by exact (by intro entry member; cases member)
theorem rowDirection336 : ∀ entry ∈ rowCases336, entry.direction = .north := by exact (by intro entry member; cases member)
theorem rowPhase336 : ∀ entry ∈ rowCases336, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases337 : List PhysicalCase := []
theorem rowFits337 : ∀ entry ∈ rowCases337, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked337 : ∀ entry ∈ rowCases337, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero337 : ∀ entry ∈ rowCases337, entry.hero = 191 := by exact (by intro entry member; cases member)
theorem rowDirection337 : ∀ entry ∈ rowCases337, entry.direction = .south := by exact (by intro entry member; cases member)
theorem rowPhase337 : ∀ entry ∈ rowCases337, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases338 : List PhysicalCase := [case279, case750]
theorem memberCase279 : case279 ∈ rowCases338 := by exact List.mem_cons_self
theorem memberCase750 : case750 ∈ rowCases338 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits338 : ∀ entry ∈ rowCases338, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case279_fitted, (List.forall_mem_cons.mpr ⟨case750_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked338 : ∀ entry ∈ rowCases338, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame279_checked, (List.forall_mem_cons.mpr ⟨frame750_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero338 : ∀ entry ∈ rowCases338, entry.hero = 191 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection338 : ∀ entry ∈ rowCases338, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase338 : ∀ entry ∈ rowCases338, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases339 : List PhysicalCase := [case280, case745]
theorem memberCase280 : case280 ∈ rowCases339 := by exact List.mem_cons_self
theorem memberCase745 : case745 ∈ rowCases339 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits339 : ∀ entry ∈ rowCases339, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case280_fitted, (List.forall_mem_cons.mpr ⟨case745_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked339 : ∀ entry ∈ rowCases339, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame280_checked, (List.forall_mem_cons.mpr ⟨frame745_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero339 : ∀ entry ∈ rowCases339, entry.hero = 191 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection339 : ∀ entry ∈ rowCases339, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase339 : ∀ entry ∈ rowCases339, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases340 : List PhysicalCase := [case281]
theorem memberCase281 : case281 ∈ rowCases340 := by exact List.mem_cons_self
theorem rowFits340 : ∀ entry ∈ rowCases340, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case281_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked340 : ∀ entry ∈ rowCases340, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame281_checked, (by intro entry member; cases member)⟩)
theorem rowHero340 : ∀ entry ∈ rowCases340, entry.hero = 191 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection340 : ∀ entry ∈ rowCases340, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase340 : ∀ entry ∈ rowCases340, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases341 : List PhysicalCase := [case282]
theorem memberCase282 : case282 ∈ rowCases341 := by exact List.mem_cons_self
theorem rowFits341 : ∀ entry ∈ rowCases341, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case282_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked341 : ∀ entry ∈ rowCases341, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame282_checked, (by intro entry member; cases member)⟩)
theorem rowHero341 : ∀ entry ∈ rowCases341, entry.hero = 191 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection341 : ∀ entry ∈ rowCases341, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase341 : ∀ entry ∈ rowCases341, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases342 : List PhysicalCase := [case283]
theorem memberCase283 : case283 ∈ rowCases342 := by exact List.mem_cons_self
theorem rowFits342 : ∀ entry ∈ rowCases342, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case283_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked342 : ∀ entry ∈ rowCases342, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame283_checked, (by intro entry member; cases member)⟩)
theorem rowHero342 : ∀ entry ∈ rowCases342, entry.hero = 191 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection342 : ∀ entry ∈ rowCases342, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase342 : ∀ entry ∈ rowCases342, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases343 : List PhysicalCase := [case284]
theorem memberCase284 : case284 ∈ rowCases343 := by exact List.mem_cons_self
theorem rowFits343 : ∀ entry ∈ rowCases343, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case284_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked343 : ∀ entry ∈ rowCases343, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame284_checked, (by intro entry member; cases member)⟩)
theorem rowHero343 : ∀ entry ∈ rowCases343, entry.hero = 191 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection343 : ∀ entry ∈ rowCases343, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase343 : ∀ entry ∈ rowCases343, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases344 : List PhysicalCase := [case285, case718]
theorem memberCase285 : case285 ∈ rowCases344 := by exact List.mem_cons_self
theorem memberCase718 : case718 ∈ rowCases344 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits344 : ∀ entry ∈ rowCases344, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case285_fitted, (List.forall_mem_cons.mpr ⟨case718_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked344 : ∀ entry ∈ rowCases344, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame285_checked, (List.forall_mem_cons.mpr ⟨frame718_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero344 : ∀ entry ∈ rowCases344, entry.hero = 192 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection344 : ∀ entry ∈ rowCases344, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase344 : ∀ entry ∈ rowCases344, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases345 : List PhysicalCase := [case286, case781]
theorem memberCase286 : case286 ∈ rowCases345 := by exact List.mem_cons_self
theorem memberCase781 : case781 ∈ rowCases345 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits345 : ∀ entry ∈ rowCases345, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case286_fitted, (List.forall_mem_cons.mpr ⟨case781_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked345 : ∀ entry ∈ rowCases345, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame286_checked, (List.forall_mem_cons.mpr ⟨frame781_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero345 : ∀ entry ∈ rowCases345, entry.hero = 192 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection345 : ∀ entry ∈ rowCases345, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase345 : ∀ entry ∈ rowCases345, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases346 : List PhysicalCase := [case287, case754]
theorem memberCase287 : case287 ∈ rowCases346 := by exact List.mem_cons_self
theorem memberCase754 : case754 ∈ rowCases346 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits346 : ∀ entry ∈ rowCases346, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case287_fitted, (List.forall_mem_cons.mpr ⟨case754_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked346 : ∀ entry ∈ rowCases346, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame287_checked, (List.forall_mem_cons.mpr ⟨frame754_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero346 : ∀ entry ∈ rowCases346, entry.hero = 192 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection346 : ∀ entry ∈ rowCases346, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase346 : ∀ entry ∈ rowCases346, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases347 : List PhysicalCase := [case288, case747]
theorem memberCase288 : case288 ∈ rowCases347 := by exact List.mem_cons_self
theorem memberCase747 : case747 ∈ rowCases347 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits347 : ∀ entry ∈ rowCases347, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case288_fitted, (List.forall_mem_cons.mpr ⟨case747_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked347 : ∀ entry ∈ rowCases347, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame288_checked, (List.forall_mem_cons.mpr ⟨frame747_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero347 : ∀ entry ∈ rowCases347, entry.hero = 192 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection347 : ∀ entry ∈ rowCases347, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase347 : ∀ entry ∈ rowCases347, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases348 : List PhysicalCase := [case289, case290]
theorem memberCase289 : case289 ∈ rowCases348 := by exact List.mem_cons_self
theorem memberCase290 : case290 ∈ rowCases348 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits348 : ∀ entry ∈ rowCases348, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case289_fitted, (List.forall_mem_cons.mpr ⟨case290_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked348 : ∀ entry ∈ rowCases348, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame289_checked, (List.forall_mem_cons.mpr ⟨frame290_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero348 : ∀ entry ∈ rowCases348, entry.hero = 192 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection348 : ∀ entry ∈ rowCases348, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase348 : ∀ entry ∈ rowCases348, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases349 : List PhysicalCase := []
theorem rowFits349 : ∀ entry ∈ rowCases349, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked349 : ∀ entry ∈ rowCases349, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero349 : ∀ entry ∈ rowCases349, entry.hero = 192 := by exact (by intro entry member; cases member)
theorem rowDirection349 : ∀ entry ∈ rowCases349, entry.direction = .northWest := by exact (by intro entry member; cases member)
theorem rowPhase349 : ∀ entry ∈ rowCases349, entry.phase = 4 := by exact (by intro entry member; cases member)
end NetHack.Soko12Forward220.Unified.P04
