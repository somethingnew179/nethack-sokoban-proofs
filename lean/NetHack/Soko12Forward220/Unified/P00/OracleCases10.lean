import NetHack.Soko12Forward220.Unified.P00.OracleCases09
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P00
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
noncomputable def rowCases500 : List PhysicalCase := [case478, case479]
theorem memberCase478 : case478 ∈ rowCases500 := by exact List.mem_cons_self
theorem memberCase479 : case479 ∈ rowCases500 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits500 : ∀ entry ∈ rowCases500, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case478_fitted, (List.forall_mem_cons.mpr ⟨case479_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked500 : ∀ entry ∈ rowCases500, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame478_checked, (List.forall_mem_cons.mpr ⟨frame479_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero500 : ∀ entry ∈ rowCases500, entry.hero = 263 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection500 : ∀ entry ∈ rowCases500, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase500 : ∀ entry ∈ rowCases500, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases501 : List PhysicalCase := [case480, case481]
theorem memberCase480 : case480 ∈ rowCases501 := by exact List.mem_cons_self
theorem memberCase481 : case481 ∈ rowCases501 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits501 : ∀ entry ∈ rowCases501, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case480_fitted, (List.forall_mem_cons.mpr ⟨case481_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked501 : ∀ entry ∈ rowCases501, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame480_checked, (List.forall_mem_cons.mpr ⟨frame481_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero501 : ∀ entry ∈ rowCases501, entry.hero = 263 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection501 : ∀ entry ∈ rowCases501, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase501 : ∀ entry ∈ rowCases501, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases502 : List PhysicalCase := [case482, case483]
theorem memberCase482 : case482 ∈ rowCases502 := by exact List.mem_cons_self
theorem memberCase483 : case483 ∈ rowCases502 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits502 : ∀ entry ∈ rowCases502, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case482_fitted, (List.forall_mem_cons.mpr ⟨case483_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked502 : ∀ entry ∈ rowCases502, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame482_checked, (List.forall_mem_cons.mpr ⟨frame483_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero502 : ∀ entry ∈ rowCases502, entry.hero = 263 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection502 : ∀ entry ∈ rowCases502, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase502 : ∀ entry ∈ rowCases502, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases503 : List PhysicalCase := [case484, case485]
theorem memberCase484 : case484 ∈ rowCases503 := by exact List.mem_cons_self
theorem memberCase485 : case485 ∈ rowCases503 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits503 : ∀ entry ∈ rowCases503, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case484_fitted, (List.forall_mem_cons.mpr ⟨case485_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked503 : ∀ entry ∈ rowCases503, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame484_checked, (List.forall_mem_cons.mpr ⟨frame485_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero503 : ∀ entry ∈ rowCases503, entry.hero = 263 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection503 : ∀ entry ∈ rowCases503, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase503 : ∀ entry ∈ rowCases503, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases504 : List PhysicalCase := [case486, case786]
theorem memberCase486 : case486 ∈ rowCases504 := by exact List.mem_cons_self
theorem memberCase786 : case786 ∈ rowCases504 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits504 : ∀ entry ∈ rowCases504, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case486_fitted, (List.forall_mem_cons.mpr ⟨case786_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked504 : ∀ entry ∈ rowCases504, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame486_checked, (List.forall_mem_cons.mpr ⟨frame786_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero504 : ∀ entry ∈ rowCases504, entry.hero = 264 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection504 : ∀ entry ∈ rowCases504, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase504 : ∀ entry ∈ rowCases504, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases505 : List PhysicalCase := [case487]
theorem memberCase487 : case487 ∈ rowCases505 := by exact List.mem_cons_self
theorem rowFits505 : ∀ entry ∈ rowCases505, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case487_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked505 : ∀ entry ∈ rowCases505, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame487_checked, (by intro entry member; cases member)⟩)
theorem rowHero505 : ∀ entry ∈ rowCases505, entry.hero = 264 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection505 : ∀ entry ∈ rowCases505, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase505 : ∀ entry ∈ rowCases505, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases506 : List PhysicalCase := [case488]
theorem memberCase488 : case488 ∈ rowCases506 := by exact List.mem_cons_self
theorem rowFits506 : ∀ entry ∈ rowCases506, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case488_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked506 : ∀ entry ∈ rowCases506, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame488_checked, (by intro entry member; cases member)⟩)
theorem rowHero506 : ∀ entry ∈ rowCases506, entry.hero = 264 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection506 : ∀ entry ∈ rowCases506, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase506 : ∀ entry ∈ rowCases506, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases507 : List PhysicalCase := [case489, case805]
theorem memberCase489 : case489 ∈ rowCases507 := by exact List.mem_cons_self
theorem memberCase805 : case805 ∈ rowCases507 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits507 : ∀ entry ∈ rowCases507, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case489_fitted, (List.forall_mem_cons.mpr ⟨case805_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked507 : ∀ entry ∈ rowCases507, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame489_checked, (List.forall_mem_cons.mpr ⟨frame805_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero507 : ∀ entry ∈ rowCases507, entry.hero = 264 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection507 : ∀ entry ∈ rowCases507, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase507 : ∀ entry ∈ rowCases507, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases508 : List PhysicalCase := [case490, case491]
theorem memberCase490 : case490 ∈ rowCases508 := by exact List.mem_cons_self
theorem memberCase491 : case491 ∈ rowCases508 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits508 : ∀ entry ∈ rowCases508, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case490_fitted, (List.forall_mem_cons.mpr ⟨case491_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked508 : ∀ entry ∈ rowCases508, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame490_checked, (List.forall_mem_cons.mpr ⟨frame491_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero508 : ∀ entry ∈ rowCases508, entry.hero = 264 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection508 : ∀ entry ∈ rowCases508, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase508 : ∀ entry ∈ rowCases508, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases509 : List PhysicalCase := [case492, case493]
theorem memberCase492 : case492 ∈ rowCases509 := by exact List.mem_cons_self
theorem memberCase493 : case493 ∈ rowCases509 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits509 : ∀ entry ∈ rowCases509, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case492_fitted, (List.forall_mem_cons.mpr ⟨case493_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked509 : ∀ entry ∈ rowCases509, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame492_checked, (List.forall_mem_cons.mpr ⟨frame493_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero509 : ∀ entry ∈ rowCases509, entry.hero = 264 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection509 : ∀ entry ∈ rowCases509, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase509 : ∀ entry ∈ rowCases509, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases510 : List PhysicalCase := [case494, case495]
theorem memberCase494 : case494 ∈ rowCases510 := by exact List.mem_cons_self
theorem memberCase495 : case495 ∈ rowCases510 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits510 : ∀ entry ∈ rowCases510, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case494_fitted, (List.forall_mem_cons.mpr ⟨case495_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked510 : ∀ entry ∈ rowCases510, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame494_checked, (List.forall_mem_cons.mpr ⟨frame495_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero510 : ∀ entry ∈ rowCases510, entry.hero = 264 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection510 : ∀ entry ∈ rowCases510, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase510 : ∀ entry ∈ rowCases510, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases511 : List PhysicalCase := [case496, case497]
theorem memberCase496 : case496 ∈ rowCases511 := by exact List.mem_cons_self
theorem memberCase497 : case497 ∈ rowCases511 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits511 : ∀ entry ∈ rowCases511, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case496_fitted, (List.forall_mem_cons.mpr ⟨case497_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked511 : ∀ entry ∈ rowCases511, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame496_checked, (List.forall_mem_cons.mpr ⟨frame497_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero511 : ∀ entry ∈ rowCases511, entry.hero = 264 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection511 : ∀ entry ∈ rowCases511, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase511 : ∀ entry ∈ rowCases511, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases512 : List PhysicalCase := [case498, case790]
theorem memberCase498 : case498 ∈ rowCases512 := by exact List.mem_cons_self
theorem memberCase790 : case790 ∈ rowCases512 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits512 : ∀ entry ∈ rowCases512, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case498_fitted, (List.forall_mem_cons.mpr ⟨case790_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked512 : ∀ entry ∈ rowCases512, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame498_checked, (List.forall_mem_cons.mpr ⟨frame790_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero512 : ∀ entry ∈ rowCases512, entry.hero = 265 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection512 : ∀ entry ∈ rowCases512, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase512 : ∀ entry ∈ rowCases512, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases513 : List PhysicalCase := [case499, case823]
theorem memberCase499 : case499 ∈ rowCases513 := by exact List.mem_cons_self
theorem memberCase823 : case823 ∈ rowCases513 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits513 : ∀ entry ∈ rowCases513, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case499_fitted, (List.forall_mem_cons.mpr ⟨case823_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked513 : ∀ entry ∈ rowCases513, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame499_checked, (List.forall_mem_cons.mpr ⟨frame823_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero513 : ∀ entry ∈ rowCases513, entry.hero = 265 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection513 : ∀ entry ∈ rowCases513, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase513 : ∀ entry ∈ rowCases513, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases514 : List PhysicalCase := []
theorem rowFits514 : ∀ entry ∈ rowCases514, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked514 : ∀ entry ∈ rowCases514, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero514 : ∀ entry ∈ rowCases514, entry.hero = 265 := by exact (by intro entry member; cases member)
theorem rowDirection514 : ∀ entry ∈ rowCases514, entry.direction = .east := by exact (by intro entry member; cases member)
theorem rowPhase514 : ∀ entry ∈ rowCases514, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases515 : List PhysicalCase := [case500, case809]
theorem memberCase500 : case500 ∈ rowCases515 := by exact List.mem_cons_self
theorem memberCase809 : case809 ∈ rowCases515 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits515 : ∀ entry ∈ rowCases515, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case500_fitted, (List.forall_mem_cons.mpr ⟨case809_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked515 : ∀ entry ∈ rowCases515, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame500_checked, (List.forall_mem_cons.mpr ⟨frame809_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero515 : ∀ entry ∈ rowCases515, entry.hero = 265 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection515 : ∀ entry ∈ rowCases515, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase515 : ∀ entry ∈ rowCases515, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases516 : List PhysicalCase := []
theorem rowFits516 : ∀ entry ∈ rowCases516, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked516 : ∀ entry ∈ rowCases516, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero516 : ∀ entry ∈ rowCases516, entry.hero = 265 := by exact (by intro entry member; cases member)
theorem rowDirection516 : ∀ entry ∈ rowCases516, entry.direction = .northEast := by exact (by intro entry member; cases member)
theorem rowPhase516 : ∀ entry ∈ rowCases516, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases517 : List PhysicalCase := [case501, case502]
theorem memberCase501 : case501 ∈ rowCases517 := by exact List.mem_cons_self
theorem memberCase502 : case502 ∈ rowCases517 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits517 : ∀ entry ∈ rowCases517, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case501_fitted, (List.forall_mem_cons.mpr ⟨case502_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked517 : ∀ entry ∈ rowCases517, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame501_checked, (List.forall_mem_cons.mpr ⟨frame502_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero517 : ∀ entry ∈ rowCases517, entry.hero = 265 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection517 : ∀ entry ∈ rowCases517, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase517 : ∀ entry ∈ rowCases517, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases518 : List PhysicalCase := [case503]
theorem memberCase503 : case503 ∈ rowCases518 := by exact List.mem_cons_self
theorem rowFits518 : ∀ entry ∈ rowCases518, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case503_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked518 : ∀ entry ∈ rowCases518, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame503_checked, (by intro entry member; cases member)⟩)
theorem rowHero518 : ∀ entry ∈ rowCases518, entry.hero = 265 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection518 : ∀ entry ∈ rowCases518, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase518 : ∀ entry ∈ rowCases518, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases519 : List PhysicalCase := [case504, case505]
theorem memberCase504 : case504 ∈ rowCases519 := by exact List.mem_cons_self
theorem memberCase505 : case505 ∈ rowCases519 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits519 : ∀ entry ∈ rowCases519, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case504_fitted, (List.forall_mem_cons.mpr ⟨case505_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked519 : ∀ entry ∈ rowCases519, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame504_checked, (List.forall_mem_cons.mpr ⟨frame505_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero519 : ∀ entry ∈ rowCases519, entry.hero = 265 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection519 : ∀ entry ∈ rowCases519, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase519 : ∀ entry ∈ rowCases519, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases520 : List PhysicalCase := [case506, case792]
theorem memberCase506 : case506 ∈ rowCases520 := by exact List.mem_cons_self
theorem memberCase792 : case792 ∈ rowCases520 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits520 : ∀ entry ∈ rowCases520, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case506_fitted, (List.forall_mem_cons.mpr ⟨case792_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked520 : ∀ entry ∈ rowCases520, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame506_checked, (List.forall_mem_cons.mpr ⟨frame792_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero520 : ∀ entry ∈ rowCases520, entry.hero = 270 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection520 : ∀ entry ∈ rowCases520, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase520 : ∀ entry ∈ rowCases520, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases521 : List PhysicalCase := [case507, case831]
theorem memberCase507 : case507 ∈ rowCases521 := by exact List.mem_cons_self
theorem memberCase831 : case831 ∈ rowCases521 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits521 : ∀ entry ∈ rowCases521, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case507_fitted, (List.forall_mem_cons.mpr ⟨case831_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked521 : ∀ entry ∈ rowCases521, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame507_checked, (List.forall_mem_cons.mpr ⟨frame831_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero521 : ∀ entry ∈ rowCases521, entry.hero = 270 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection521 : ∀ entry ∈ rowCases521, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase521 : ∀ entry ∈ rowCases521, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases522 : List PhysicalCase := [case508, case816]
theorem memberCase508 : case508 ∈ rowCases522 := by exact List.mem_cons_self
theorem memberCase816 : case816 ∈ rowCases522 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits522 : ∀ entry ∈ rowCases522, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case508_fitted, (List.forall_mem_cons.mpr ⟨case816_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked522 : ∀ entry ∈ rowCases522, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame508_checked, (List.forall_mem_cons.mpr ⟨frame816_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero522 : ∀ entry ∈ rowCases522, entry.hero = 270 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection522 : ∀ entry ∈ rowCases522, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase522 : ∀ entry ∈ rowCases522, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases523 : List PhysicalCase := []
theorem rowFits523 : ∀ entry ∈ rowCases523, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked523 : ∀ entry ∈ rowCases523, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero523 : ∀ entry ∈ rowCases523, entry.hero = 270 := by exact (by intro entry member; cases member)
theorem rowDirection523 : ∀ entry ∈ rowCases523, entry.direction = .west := by exact (by intro entry member; cases member)
theorem rowPhase523 : ∀ entry ∈ rowCases523, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases524 : List PhysicalCase := [case509, case510]
theorem memberCase509 : case509 ∈ rowCases524 := by exact List.mem_cons_self
theorem memberCase510 : case510 ∈ rowCases524 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits524 : ∀ entry ∈ rowCases524, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case509_fitted, (List.forall_mem_cons.mpr ⟨case510_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked524 : ∀ entry ∈ rowCases524, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame509_checked, (List.forall_mem_cons.mpr ⟨frame510_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero524 : ∀ entry ∈ rowCases524, entry.hero = 270 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection524 : ∀ entry ∈ rowCases524, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase524 : ∀ entry ∈ rowCases524, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases525 : List PhysicalCase := []
theorem rowFits525 : ∀ entry ∈ rowCases525, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked525 : ∀ entry ∈ rowCases525, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero525 : ∀ entry ∈ rowCases525, entry.hero = 270 := by exact (by intro entry member; cases member)
theorem rowDirection525 : ∀ entry ∈ rowCases525, entry.direction = .northWest := by exact (by intro entry member; cases member)
theorem rowPhase525 : ∀ entry ∈ rowCases525, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases526 : List PhysicalCase := [case511, case512]
theorem memberCase511 : case511 ∈ rowCases526 := by exact List.mem_cons_self
theorem memberCase512 : case512 ∈ rowCases526 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits526 : ∀ entry ∈ rowCases526, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case511_fitted, (List.forall_mem_cons.mpr ⟨case512_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked526 : ∀ entry ∈ rowCases526, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame511_checked, (List.forall_mem_cons.mpr ⟨frame512_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero526 : ∀ entry ∈ rowCases526, entry.hero = 270 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection526 : ∀ entry ∈ rowCases526, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase526 : ∀ entry ∈ rowCases526, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases527 : List PhysicalCase := []
theorem rowFits527 : ∀ entry ∈ rowCases527, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked527 : ∀ entry ∈ rowCases527, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero527 : ∀ entry ∈ rowCases527, entry.hero = 270 := by exact (by intro entry member; cases member)
theorem rowDirection527 : ∀ entry ∈ rowCases527, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase527 : ∀ entry ∈ rowCases527, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases528 : List PhysicalCase := [case513, case794]
theorem memberCase513 : case513 ∈ rowCases528 := by exact List.mem_cons_self
theorem memberCase794 : case794 ∈ rowCases528 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits528 : ∀ entry ∈ rowCases528, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case513_fitted, (List.forall_mem_cons.mpr ⟨case794_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked528 : ∀ entry ∈ rowCases528, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame513_checked, (List.forall_mem_cons.mpr ⟨frame794_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero528 : ∀ entry ∈ rowCases528, entry.hero = 271 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection528 : ∀ entry ∈ rowCases528, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase528 : ∀ entry ∈ rowCases528, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases529 : List PhysicalCase := [case514]
theorem memberCase514 : case514 ∈ rowCases529 := by exact List.mem_cons_self
theorem rowFits529 : ∀ entry ∈ rowCases529, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case514_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked529 : ∀ entry ∈ rowCases529, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame514_checked, (by intro entry member; cases member)⟩)
theorem rowHero529 : ∀ entry ∈ rowCases529, entry.hero = 271 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection529 : ∀ entry ∈ rowCases529, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase529 : ∀ entry ∈ rowCases529, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases530 : List PhysicalCase := [case515]
theorem memberCase515 : case515 ∈ rowCases530 := by exact List.mem_cons_self
theorem rowFits530 : ∀ entry ∈ rowCases530, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case515_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked530 : ∀ entry ∈ rowCases530, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame515_checked, (by intro entry member; cases member)⟩)
theorem rowHero530 : ∀ entry ∈ rowCases530, entry.hero = 271 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection530 : ∀ entry ∈ rowCases530, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase530 : ∀ entry ∈ rowCases530, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases531 : List PhysicalCase := [case516]
theorem memberCase516 : case516 ∈ rowCases531 := by exact List.mem_cons_self
theorem rowFits531 : ∀ entry ∈ rowCases531, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case516_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked531 : ∀ entry ∈ rowCases531, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame516_checked, (by intro entry member; cases member)⟩)
theorem rowHero531 : ∀ entry ∈ rowCases531, entry.hero = 271 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection531 : ∀ entry ∈ rowCases531, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase531 : ∀ entry ∈ rowCases531, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases532 : List PhysicalCase := [case517, case518]
theorem memberCase517 : case517 ∈ rowCases532 := by exact List.mem_cons_self
theorem memberCase518 : case518 ∈ rowCases532 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits532 : ∀ entry ∈ rowCases532, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case517_fitted, (List.forall_mem_cons.mpr ⟨case518_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked532 : ∀ entry ∈ rowCases532, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame517_checked, (List.forall_mem_cons.mpr ⟨frame518_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero532 : ∀ entry ∈ rowCases532, entry.hero = 271 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection532 : ∀ entry ∈ rowCases532, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase532 : ∀ entry ∈ rowCases532, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases533 : List PhysicalCase := [case519, case520]
theorem memberCase519 : case519 ∈ rowCases533 := by exact List.mem_cons_self
theorem memberCase520 : case520 ∈ rowCases533 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits533 : ∀ entry ∈ rowCases533, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case519_fitted, (List.forall_mem_cons.mpr ⟨case520_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked533 : ∀ entry ∈ rowCases533, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame519_checked, (List.forall_mem_cons.mpr ⟨frame520_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero533 : ∀ entry ∈ rowCases533, entry.hero = 271 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection533 : ∀ entry ∈ rowCases533, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase533 : ∀ entry ∈ rowCases533, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases534 : List PhysicalCase := []
theorem rowFits534 : ∀ entry ∈ rowCases534, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked534 : ∀ entry ∈ rowCases534, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero534 : ∀ entry ∈ rowCases534, entry.hero = 271 := by exact (by intro entry member; cases member)
theorem rowDirection534 : ∀ entry ∈ rowCases534, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase534 : ∀ entry ∈ rowCases534, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases535 : List PhysicalCase := [case521, case522]
theorem memberCase521 : case521 ∈ rowCases535 := by exact List.mem_cons_self
theorem memberCase522 : case522 ∈ rowCases535 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits535 : ∀ entry ∈ rowCases535, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case521_fitted, (List.forall_mem_cons.mpr ⟨case522_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked535 : ∀ entry ∈ rowCases535, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame521_checked, (List.forall_mem_cons.mpr ⟨frame522_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero535 : ∀ entry ∈ rowCases535, entry.hero = 271 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection535 : ∀ entry ∈ rowCases535, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase535 : ∀ entry ∈ rowCases535, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases536 : List PhysicalCase := [case523, case798]
theorem memberCase523 : case523 ∈ rowCases536 := by exact List.mem_cons_self
theorem memberCase798 : case798 ∈ rowCases536 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits536 : ∀ entry ∈ rowCases536, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case523_fitted, (List.forall_mem_cons.mpr ⟨case798_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked536 : ∀ entry ∈ rowCases536, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame523_checked, (List.forall_mem_cons.mpr ⟨frame798_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero536 : ∀ entry ∈ rowCases536, entry.hero = 272 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection536 : ∀ entry ∈ rowCases536, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase536 : ∀ entry ∈ rowCases536, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases537 : List PhysicalCase := []
theorem rowFits537 : ∀ entry ∈ rowCases537, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked537 : ∀ entry ∈ rowCases537, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero537 : ∀ entry ∈ rowCases537, entry.hero = 272 := by exact (by intro entry member; cases member)
theorem rowDirection537 : ∀ entry ∈ rowCases537, entry.direction = .south := by exact (by intro entry member; cases member)
theorem rowPhase537 : ∀ entry ∈ rowCases537, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases538 : List PhysicalCase := []
theorem rowFits538 : ∀ entry ∈ rowCases538, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked538 : ∀ entry ∈ rowCases538, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero538 : ∀ entry ∈ rowCases538, entry.hero = 272 := by exact (by intro entry member; cases member)
theorem rowDirection538 : ∀ entry ∈ rowCases538, entry.direction = .east := by exact (by intro entry member; cases member)
theorem rowPhase538 : ∀ entry ∈ rowCases538, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases539 : List PhysicalCase := [case524, case817]
theorem memberCase524 : case524 ∈ rowCases539 := by exact List.mem_cons_self
theorem memberCase817 : case817 ∈ rowCases539 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits539 : ∀ entry ∈ rowCases539, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case524_fitted, (List.forall_mem_cons.mpr ⟨case817_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked539 : ∀ entry ∈ rowCases539, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame524_checked, (List.forall_mem_cons.mpr ⟨frame817_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero539 : ∀ entry ∈ rowCases539, entry.hero = 272 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection539 : ∀ entry ∈ rowCases539, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase539 : ∀ entry ∈ rowCases539, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases540 : List PhysicalCase := []
theorem rowFits540 : ∀ entry ∈ rowCases540, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked540 : ∀ entry ∈ rowCases540, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero540 : ∀ entry ∈ rowCases540, entry.hero = 272 := by exact (by intro entry member; cases member)
theorem rowDirection540 : ∀ entry ∈ rowCases540, entry.direction = .northEast := by exact (by intro entry member; cases member)
theorem rowPhase540 : ∀ entry ∈ rowCases540, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases541 : List PhysicalCase := [case525, case526]
theorem memberCase525 : case525 ∈ rowCases541 := by exact List.mem_cons_self
theorem memberCase526 : case526 ∈ rowCases541 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits541 : ∀ entry ∈ rowCases541, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case525_fitted, (List.forall_mem_cons.mpr ⟨case526_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked541 : ∀ entry ∈ rowCases541, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame525_checked, (List.forall_mem_cons.mpr ⟨frame526_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero541 : ∀ entry ∈ rowCases541, entry.hero = 272 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection541 : ∀ entry ∈ rowCases541, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase541 : ∀ entry ∈ rowCases541, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases542 : List PhysicalCase := []
theorem rowFits542 : ∀ entry ∈ rowCases542, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked542 : ∀ entry ∈ rowCases542, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero542 : ∀ entry ∈ rowCases542, entry.hero = 272 := by exact (by intro entry member; cases member)
theorem rowDirection542 : ∀ entry ∈ rowCases542, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase542 : ∀ entry ∈ rowCases542, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases543 : List PhysicalCase := [case527]
theorem memberCase527 : case527 ∈ rowCases543 := by exact List.mem_cons_self
theorem rowFits543 : ∀ entry ∈ rowCases543, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case527_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked543 : ∀ entry ∈ rowCases543, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame527_checked, (by intro entry member; cases member)⟩)
theorem rowHero543 : ∀ entry ∈ rowCases543, entry.hero = 272 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection543 : ∀ entry ∈ rowCases543, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase543 : ∀ entry ∈ rowCases543, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases544 : List PhysicalCase := [case528, case800]
theorem memberCase528 : case528 ∈ rowCases544 := by exact List.mem_cons_self
theorem memberCase800 : case800 ∈ rowCases544 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits544 : ∀ entry ∈ rowCases544, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case528_fitted, (List.forall_mem_cons.mpr ⟨case800_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked544 : ∀ entry ∈ rowCases544, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame528_checked, (List.forall_mem_cons.mpr ⟨frame800_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero544 : ∀ entry ∈ rowCases544, entry.hero = 288 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection544 : ∀ entry ∈ rowCases544, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase544 : ∀ entry ∈ rowCases544, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases545 : List PhysicalCase := []
theorem rowFits545 : ∀ entry ∈ rowCases545, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked545 : ∀ entry ∈ rowCases545, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero545 : ∀ entry ∈ rowCases545, entry.hero = 288 := by exact (by intro entry member; cases member)
theorem rowDirection545 : ∀ entry ∈ rowCases545, entry.direction = .south := by exact (by intro entry member; cases member)
theorem rowPhase545 : ∀ entry ∈ rowCases545, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases546 : List PhysicalCase := [case529, case818]
theorem memberCase529 : case529 ∈ rowCases546 := by exact List.mem_cons_self
theorem memberCase818 : case818 ∈ rowCases546 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits546 : ∀ entry ∈ rowCases546, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case529_fitted, (List.forall_mem_cons.mpr ⟨case818_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked546 : ∀ entry ∈ rowCases546, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame529_checked, (List.forall_mem_cons.mpr ⟨frame818_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero546 : ∀ entry ∈ rowCases546, entry.hero = 288 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection546 : ∀ entry ∈ rowCases546, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase546 : ∀ entry ∈ rowCases546, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases547 : List PhysicalCase := []
theorem rowFits547 : ∀ entry ∈ rowCases547, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked547 : ∀ entry ∈ rowCases547, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero547 : ∀ entry ∈ rowCases547, entry.hero = 288 := by exact (by intro entry member; cases member)
theorem rowDirection547 : ∀ entry ∈ rowCases547, entry.direction = .west := by exact (by intro entry member; cases member)
theorem rowPhase547 : ∀ entry ∈ rowCases547, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases548 : List PhysicalCase := [case530, case531]
theorem memberCase530 : case530 ∈ rowCases548 := by exact List.mem_cons_self
theorem memberCase531 : case531 ∈ rowCases548 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits548 : ∀ entry ∈ rowCases548, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case530_fitted, (List.forall_mem_cons.mpr ⟨case531_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked548 : ∀ entry ∈ rowCases548, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame530_checked, (List.forall_mem_cons.mpr ⟨frame531_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero548 : ∀ entry ∈ rowCases548, entry.hero = 288 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection548 : ∀ entry ∈ rowCases548, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase548 : ∀ entry ∈ rowCases548, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases549 : List PhysicalCase := []
theorem rowFits549 : ∀ entry ∈ rowCases549, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked549 : ∀ entry ∈ rowCases549, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero549 : ∀ entry ∈ rowCases549, entry.hero = 288 := by exact (by intro entry member; cases member)
theorem rowDirection549 : ∀ entry ∈ rowCases549, entry.direction = .northWest := by exact (by intro entry member; cases member)
theorem rowPhase549 : ∀ entry ∈ rowCases549, entry.phase = 0 := by exact (by intro entry member; cases member)
end NetHack.Soko12Forward220.Unified.P00
