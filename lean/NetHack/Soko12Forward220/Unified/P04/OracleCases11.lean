import NetHack.Soko12Forward220.Unified.P04.OracleCases10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P04
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
noncomputable def rowCases550 : List PhysicalCase := [case511]
theorem memberCase511 : case511 ∈ rowCases550 := by exact List.mem_cons_self
theorem rowFits550 : ∀ entry ∈ rowCases550, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case511_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked550 : ∀ entry ∈ rowCases550, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame511_checked, (by intro entry member; cases member)⟩)
theorem rowHero550 : ∀ entry ∈ rowCases550, entry.hero = 265 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection550 : ∀ entry ∈ rowCases550, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase550 : ∀ entry ∈ rowCases550, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases551 : List PhysicalCase := [case512, case513]
theorem memberCase512 : case512 ∈ rowCases551 := by exact List.mem_cons_self
theorem memberCase513 : case513 ∈ rowCases551 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits551 : ∀ entry ∈ rowCases551, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case512_fitted, (List.forall_mem_cons.mpr ⟨case513_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked551 : ∀ entry ∈ rowCases551, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame512_checked, (List.forall_mem_cons.mpr ⟨frame513_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero551 : ∀ entry ∈ rowCases551, entry.hero = 265 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection551 : ∀ entry ∈ rowCases551, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase551 : ∀ entry ∈ rowCases551, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases552 : List PhysicalCase := [case514, case800]
theorem memberCase514 : case514 ∈ rowCases552 := by exact List.mem_cons_self
theorem memberCase800 : case800 ∈ rowCases552 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits552 : ∀ entry ∈ rowCases552, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case514_fitted, (List.forall_mem_cons.mpr ⟨case800_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked552 : ∀ entry ∈ rowCases552, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame514_checked, (List.forall_mem_cons.mpr ⟨frame800_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero552 : ∀ entry ∈ rowCases552, entry.hero = 270 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection552 : ∀ entry ∈ rowCases552, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase552 : ∀ entry ∈ rowCases552, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases553 : List PhysicalCase := [case515, case839]
theorem memberCase515 : case515 ∈ rowCases553 := by exact List.mem_cons_self
theorem memberCase839 : case839 ∈ rowCases553 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits553 : ∀ entry ∈ rowCases553, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case515_fitted, (List.forall_mem_cons.mpr ⟨case839_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked553 : ∀ entry ∈ rowCases553, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame515_checked, (List.forall_mem_cons.mpr ⟨frame839_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero553 : ∀ entry ∈ rowCases553, entry.hero = 270 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection553 : ∀ entry ∈ rowCases553, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase553 : ∀ entry ∈ rowCases553, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases554 : List PhysicalCase := [case516, case824]
theorem memberCase516 : case516 ∈ rowCases554 := by exact List.mem_cons_self
theorem memberCase824 : case824 ∈ rowCases554 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits554 : ∀ entry ∈ rowCases554, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case516_fitted, (List.forall_mem_cons.mpr ⟨case824_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked554 : ∀ entry ∈ rowCases554, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame516_checked, (List.forall_mem_cons.mpr ⟨frame824_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero554 : ∀ entry ∈ rowCases554, entry.hero = 270 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection554 : ∀ entry ∈ rowCases554, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase554 : ∀ entry ∈ rowCases554, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases555 : List PhysicalCase := []
theorem rowFits555 : ∀ entry ∈ rowCases555, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked555 : ∀ entry ∈ rowCases555, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero555 : ∀ entry ∈ rowCases555, entry.hero = 270 := by exact (by intro entry member; cases member)
theorem rowDirection555 : ∀ entry ∈ rowCases555, entry.direction = .west := by exact (by intro entry member; cases member)
theorem rowPhase555 : ∀ entry ∈ rowCases555, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases556 : List PhysicalCase := [case517, case518]
theorem memberCase517 : case517 ∈ rowCases556 := by exact List.mem_cons_self
theorem memberCase518 : case518 ∈ rowCases556 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits556 : ∀ entry ∈ rowCases556, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case517_fitted, (List.forall_mem_cons.mpr ⟨case518_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked556 : ∀ entry ∈ rowCases556, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame517_checked, (List.forall_mem_cons.mpr ⟨frame518_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero556 : ∀ entry ∈ rowCases556, entry.hero = 270 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection556 : ∀ entry ∈ rowCases556, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase556 : ∀ entry ∈ rowCases556, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases557 : List PhysicalCase := []
theorem rowFits557 : ∀ entry ∈ rowCases557, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked557 : ∀ entry ∈ rowCases557, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero557 : ∀ entry ∈ rowCases557, entry.hero = 270 := by exact (by intro entry member; cases member)
theorem rowDirection557 : ∀ entry ∈ rowCases557, entry.direction = .northWest := by exact (by intro entry member; cases member)
theorem rowPhase557 : ∀ entry ∈ rowCases557, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases558 : List PhysicalCase := [case519, case520]
theorem memberCase519 : case519 ∈ rowCases558 := by exact List.mem_cons_self
theorem memberCase520 : case520 ∈ rowCases558 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits558 : ∀ entry ∈ rowCases558, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case519_fitted, (List.forall_mem_cons.mpr ⟨case520_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked558 : ∀ entry ∈ rowCases558, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame519_checked, (List.forall_mem_cons.mpr ⟨frame520_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero558 : ∀ entry ∈ rowCases558, entry.hero = 270 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection558 : ∀ entry ∈ rowCases558, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase558 : ∀ entry ∈ rowCases558, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases559 : List PhysicalCase := []
theorem rowFits559 : ∀ entry ∈ rowCases559, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked559 : ∀ entry ∈ rowCases559, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero559 : ∀ entry ∈ rowCases559, entry.hero = 270 := by exact (by intro entry member; cases member)
theorem rowDirection559 : ∀ entry ∈ rowCases559, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase559 : ∀ entry ∈ rowCases559, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases560 : List PhysicalCase := [case521, case802]
theorem memberCase521 : case521 ∈ rowCases560 := by exact List.mem_cons_self
theorem memberCase802 : case802 ∈ rowCases560 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits560 : ∀ entry ∈ rowCases560, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case521_fitted, (List.forall_mem_cons.mpr ⟨case802_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked560 : ∀ entry ∈ rowCases560, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame521_checked, (List.forall_mem_cons.mpr ⟨frame802_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero560 : ∀ entry ∈ rowCases560, entry.hero = 271 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection560 : ∀ entry ∈ rowCases560, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase560 : ∀ entry ∈ rowCases560, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases561 : List PhysicalCase := [case522]
theorem memberCase522 : case522 ∈ rowCases561 := by exact List.mem_cons_self
theorem rowFits561 : ∀ entry ∈ rowCases561, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case522_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked561 : ∀ entry ∈ rowCases561, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame522_checked, (by intro entry member; cases member)⟩)
theorem rowHero561 : ∀ entry ∈ rowCases561, entry.hero = 271 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection561 : ∀ entry ∈ rowCases561, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase561 : ∀ entry ∈ rowCases561, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases562 : List PhysicalCase := [case523]
theorem memberCase523 : case523 ∈ rowCases562 := by exact List.mem_cons_self
theorem rowFits562 : ∀ entry ∈ rowCases562, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case523_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked562 : ∀ entry ∈ rowCases562, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame523_checked, (by intro entry member; cases member)⟩)
theorem rowHero562 : ∀ entry ∈ rowCases562, entry.hero = 271 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection562 : ∀ entry ∈ rowCases562, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase562 : ∀ entry ∈ rowCases562, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases563 : List PhysicalCase := [case524]
theorem memberCase524 : case524 ∈ rowCases563 := by exact List.mem_cons_self
theorem rowFits563 : ∀ entry ∈ rowCases563, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case524_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked563 : ∀ entry ∈ rowCases563, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame524_checked, (by intro entry member; cases member)⟩)
theorem rowHero563 : ∀ entry ∈ rowCases563, entry.hero = 271 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection563 : ∀ entry ∈ rowCases563, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase563 : ∀ entry ∈ rowCases563, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases564 : List PhysicalCase := [case525, case526]
theorem memberCase525 : case525 ∈ rowCases564 := by exact List.mem_cons_self
theorem memberCase526 : case526 ∈ rowCases564 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits564 : ∀ entry ∈ rowCases564, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case525_fitted, (List.forall_mem_cons.mpr ⟨case526_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked564 : ∀ entry ∈ rowCases564, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame525_checked, (List.forall_mem_cons.mpr ⟨frame526_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero564 : ∀ entry ∈ rowCases564, entry.hero = 271 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection564 : ∀ entry ∈ rowCases564, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase564 : ∀ entry ∈ rowCases564, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases565 : List PhysicalCase := [case527, case528]
theorem memberCase527 : case527 ∈ rowCases565 := by exact List.mem_cons_self
theorem memberCase528 : case528 ∈ rowCases565 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits565 : ∀ entry ∈ rowCases565, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case527_fitted, (List.forall_mem_cons.mpr ⟨case528_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked565 : ∀ entry ∈ rowCases565, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame527_checked, (List.forall_mem_cons.mpr ⟨frame528_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero565 : ∀ entry ∈ rowCases565, entry.hero = 271 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection565 : ∀ entry ∈ rowCases565, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase565 : ∀ entry ∈ rowCases565, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases566 : List PhysicalCase := []
theorem rowFits566 : ∀ entry ∈ rowCases566, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked566 : ∀ entry ∈ rowCases566, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero566 : ∀ entry ∈ rowCases566, entry.hero = 271 := by exact (by intro entry member; cases member)
theorem rowDirection566 : ∀ entry ∈ rowCases566, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase566 : ∀ entry ∈ rowCases566, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases567 : List PhysicalCase := [case529, case530]
theorem memberCase529 : case529 ∈ rowCases567 := by exact List.mem_cons_self
theorem memberCase530 : case530 ∈ rowCases567 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits567 : ∀ entry ∈ rowCases567, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case529_fitted, (List.forall_mem_cons.mpr ⟨case530_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked567 : ∀ entry ∈ rowCases567, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame529_checked, (List.forall_mem_cons.mpr ⟨frame530_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero567 : ∀ entry ∈ rowCases567, entry.hero = 271 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection567 : ∀ entry ∈ rowCases567, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase567 : ∀ entry ∈ rowCases567, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases568 : List PhysicalCase := [case531, case806]
theorem memberCase531 : case531 ∈ rowCases568 := by exact List.mem_cons_self
theorem memberCase806 : case806 ∈ rowCases568 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits568 : ∀ entry ∈ rowCases568, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case531_fitted, (List.forall_mem_cons.mpr ⟨case806_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked568 : ∀ entry ∈ rowCases568, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame531_checked, (List.forall_mem_cons.mpr ⟨frame806_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero568 : ∀ entry ∈ rowCases568, entry.hero = 272 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection568 : ∀ entry ∈ rowCases568, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase568 : ∀ entry ∈ rowCases568, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases569 : List PhysicalCase := []
theorem rowFits569 : ∀ entry ∈ rowCases569, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked569 : ∀ entry ∈ rowCases569, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero569 : ∀ entry ∈ rowCases569, entry.hero = 272 := by exact (by intro entry member; cases member)
theorem rowDirection569 : ∀ entry ∈ rowCases569, entry.direction = .south := by exact (by intro entry member; cases member)
theorem rowPhase569 : ∀ entry ∈ rowCases569, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases570 : List PhysicalCase := []
theorem rowFits570 : ∀ entry ∈ rowCases570, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked570 : ∀ entry ∈ rowCases570, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero570 : ∀ entry ∈ rowCases570, entry.hero = 272 := by exact (by intro entry member; cases member)
theorem rowDirection570 : ∀ entry ∈ rowCases570, entry.direction = .east := by exact (by intro entry member; cases member)
theorem rowPhase570 : ∀ entry ∈ rowCases570, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases571 : List PhysicalCase := [case532, case825]
theorem memberCase532 : case532 ∈ rowCases571 := by exact List.mem_cons_self
theorem memberCase825 : case825 ∈ rowCases571 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits571 : ∀ entry ∈ rowCases571, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case532_fitted, (List.forall_mem_cons.mpr ⟨case825_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked571 : ∀ entry ∈ rowCases571, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame532_checked, (List.forall_mem_cons.mpr ⟨frame825_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero571 : ∀ entry ∈ rowCases571, entry.hero = 272 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection571 : ∀ entry ∈ rowCases571, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase571 : ∀ entry ∈ rowCases571, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases572 : List PhysicalCase := []
theorem rowFits572 : ∀ entry ∈ rowCases572, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked572 : ∀ entry ∈ rowCases572, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero572 : ∀ entry ∈ rowCases572, entry.hero = 272 := by exact (by intro entry member; cases member)
theorem rowDirection572 : ∀ entry ∈ rowCases572, entry.direction = .northEast := by exact (by intro entry member; cases member)
theorem rowPhase572 : ∀ entry ∈ rowCases572, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases573 : List PhysicalCase := [case533, case534]
theorem memberCase533 : case533 ∈ rowCases573 := by exact List.mem_cons_self
theorem memberCase534 : case534 ∈ rowCases573 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits573 : ∀ entry ∈ rowCases573, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case533_fitted, (List.forall_mem_cons.mpr ⟨case534_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked573 : ∀ entry ∈ rowCases573, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame533_checked, (List.forall_mem_cons.mpr ⟨frame534_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero573 : ∀ entry ∈ rowCases573, entry.hero = 272 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection573 : ∀ entry ∈ rowCases573, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase573 : ∀ entry ∈ rowCases573, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases574 : List PhysicalCase := []
theorem rowFits574 : ∀ entry ∈ rowCases574, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked574 : ∀ entry ∈ rowCases574, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero574 : ∀ entry ∈ rowCases574, entry.hero = 272 := by exact (by intro entry member; cases member)
theorem rowDirection574 : ∀ entry ∈ rowCases574, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase574 : ∀ entry ∈ rowCases574, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases575 : List PhysicalCase := [case535]
theorem memberCase535 : case535 ∈ rowCases575 := by exact List.mem_cons_self
theorem rowFits575 : ∀ entry ∈ rowCases575, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case535_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked575 : ∀ entry ∈ rowCases575, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame535_checked, (by intro entry member; cases member)⟩)
theorem rowHero575 : ∀ entry ∈ rowCases575, entry.hero = 272 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection575 : ∀ entry ∈ rowCases575, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase575 : ∀ entry ∈ rowCases575, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases576 : List PhysicalCase := [case536, case808]
theorem memberCase536 : case536 ∈ rowCases576 := by exact List.mem_cons_self
theorem memberCase808 : case808 ∈ rowCases576 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits576 : ∀ entry ∈ rowCases576, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case536_fitted, (List.forall_mem_cons.mpr ⟨case808_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked576 : ∀ entry ∈ rowCases576, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame536_checked, (List.forall_mem_cons.mpr ⟨frame808_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero576 : ∀ entry ∈ rowCases576, entry.hero = 288 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection576 : ∀ entry ∈ rowCases576, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase576 : ∀ entry ∈ rowCases576, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases577 : List PhysicalCase := []
theorem rowFits577 : ∀ entry ∈ rowCases577, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked577 : ∀ entry ∈ rowCases577, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero577 : ∀ entry ∈ rowCases577, entry.hero = 288 := by exact (by intro entry member; cases member)
theorem rowDirection577 : ∀ entry ∈ rowCases577, entry.direction = .south := by exact (by intro entry member; cases member)
theorem rowPhase577 : ∀ entry ∈ rowCases577, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases578 : List PhysicalCase := [case537, case826]
theorem memberCase537 : case537 ∈ rowCases578 := by exact List.mem_cons_self
theorem memberCase826 : case826 ∈ rowCases578 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits578 : ∀ entry ∈ rowCases578, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case537_fitted, (List.forall_mem_cons.mpr ⟨case826_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked578 : ∀ entry ∈ rowCases578, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame537_checked, (List.forall_mem_cons.mpr ⟨frame826_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero578 : ∀ entry ∈ rowCases578, entry.hero = 288 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection578 : ∀ entry ∈ rowCases578, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase578 : ∀ entry ∈ rowCases578, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases579 : List PhysicalCase := []
theorem rowFits579 : ∀ entry ∈ rowCases579, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked579 : ∀ entry ∈ rowCases579, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero579 : ∀ entry ∈ rowCases579, entry.hero = 288 := by exact (by intro entry member; cases member)
theorem rowDirection579 : ∀ entry ∈ rowCases579, entry.direction = .west := by exact (by intro entry member; cases member)
theorem rowPhase579 : ∀ entry ∈ rowCases579, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases580 : List PhysicalCase := [case538, case539]
theorem memberCase538 : case538 ∈ rowCases580 := by exact List.mem_cons_self
theorem memberCase539 : case539 ∈ rowCases580 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits580 : ∀ entry ∈ rowCases580, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case538_fitted, (List.forall_mem_cons.mpr ⟨case539_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked580 : ∀ entry ∈ rowCases580, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame538_checked, (List.forall_mem_cons.mpr ⟨frame539_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero580 : ∀ entry ∈ rowCases580, entry.hero = 288 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection580 : ∀ entry ∈ rowCases580, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase580 : ∀ entry ∈ rowCases580, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases581 : List PhysicalCase := []
theorem rowFits581 : ∀ entry ∈ rowCases581, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked581 : ∀ entry ∈ rowCases581, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero581 : ∀ entry ∈ rowCases581, entry.hero = 288 := by exact (by intro entry member; cases member)
theorem rowDirection581 : ∀ entry ∈ rowCases581, entry.direction = .northWest := by exact (by intro entry member; cases member)
theorem rowPhase581 : ∀ entry ∈ rowCases581, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases582 : List PhysicalCase := []
theorem rowFits582 : ∀ entry ∈ rowCases582, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked582 : ∀ entry ∈ rowCases582, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero582 : ∀ entry ∈ rowCases582, entry.hero = 288 := by exact (by intro entry member; cases member)
theorem rowDirection582 : ∀ entry ∈ rowCases582, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase582 : ∀ entry ∈ rowCases582, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases583 : List PhysicalCase := []
theorem rowFits583 : ∀ entry ∈ rowCases583, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked583 : ∀ entry ∈ rowCases583, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero583 : ∀ entry ∈ rowCases583, entry.hero = 288 := by exact (by intro entry member; cases member)
theorem rowDirection583 : ∀ entry ∈ rowCases583, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase583 : ∀ entry ∈ rowCases583, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases584 : List PhysicalCase := [case540, case810]
theorem memberCase540 : case540 ∈ rowCases584 := by exact List.mem_cons_self
theorem memberCase810 : case810 ∈ rowCases584 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits584 : ∀ entry ∈ rowCases584, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case540_fitted, (List.forall_mem_cons.mpr ⟨case810_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked584 : ∀ entry ∈ rowCases584, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame540_checked, (List.forall_mem_cons.mpr ⟨frame810_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero584 : ∀ entry ∈ rowCases584, entry.hero = 289 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection584 : ∀ entry ∈ rowCases584, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase584 : ∀ entry ∈ rowCases584, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases585 : List PhysicalCase := []
theorem rowFits585 : ∀ entry ∈ rowCases585, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked585 : ∀ entry ∈ rowCases585, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero585 : ∀ entry ∈ rowCases585, entry.hero = 289 := by exact (by intro entry member; cases member)
theorem rowDirection585 : ∀ entry ∈ rowCases585, entry.direction = .south := by exact (by intro entry member; cases member)
theorem rowPhase585 : ∀ entry ∈ rowCases585, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases586 : List PhysicalCase := [case541, case828]
theorem memberCase541 : case541 ∈ rowCases586 := by exact List.mem_cons_self
theorem memberCase828 : case828 ∈ rowCases586 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits586 : ∀ entry ∈ rowCases586, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case541_fitted, (List.forall_mem_cons.mpr ⟨case828_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked586 : ∀ entry ∈ rowCases586, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame541_checked, (List.forall_mem_cons.mpr ⟨frame828_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero586 : ∀ entry ∈ rowCases586, entry.hero = 289 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection586 : ∀ entry ∈ rowCases586, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase586 : ∀ entry ∈ rowCases586, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases587 : List PhysicalCase := [case542]
theorem memberCase542 : case542 ∈ rowCases587 := by exact List.mem_cons_self
theorem rowFits587 : ∀ entry ∈ rowCases587, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case542_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked587 : ∀ entry ∈ rowCases587, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame542_checked, (by intro entry member; cases member)⟩)
theorem rowHero587 : ∀ entry ∈ rowCases587, entry.hero = 289 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection587 : ∀ entry ∈ rowCases587, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase587 : ∀ entry ∈ rowCases587, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases588 : List PhysicalCase := [case543, case544]
theorem memberCase543 : case543 ∈ rowCases588 := by exact List.mem_cons_self
theorem memberCase544 : case544 ∈ rowCases588 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits588 : ∀ entry ∈ rowCases588, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case543_fitted, (List.forall_mem_cons.mpr ⟨case544_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked588 : ∀ entry ∈ rowCases588, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame543_checked, (List.forall_mem_cons.mpr ⟨frame544_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero588 : ∀ entry ∈ rowCases588, entry.hero = 289 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection588 : ∀ entry ∈ rowCases588, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase588 : ∀ entry ∈ rowCases588, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases589 : List PhysicalCase := [case545, case546]
theorem memberCase545 : case545 ∈ rowCases589 := by exact List.mem_cons_self
theorem memberCase546 : case546 ∈ rowCases589 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits589 : ∀ entry ∈ rowCases589, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case545_fitted, (List.forall_mem_cons.mpr ⟨case546_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked589 : ∀ entry ∈ rowCases589, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame545_checked, (List.forall_mem_cons.mpr ⟨frame546_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero589 : ∀ entry ∈ rowCases589, entry.hero = 289 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection589 : ∀ entry ∈ rowCases589, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase589 : ∀ entry ∈ rowCases589, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases590 : List PhysicalCase := []
theorem rowFits590 : ∀ entry ∈ rowCases590, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked590 : ∀ entry ∈ rowCases590, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero590 : ∀ entry ∈ rowCases590, entry.hero = 289 := by exact (by intro entry member; cases member)
theorem rowDirection590 : ∀ entry ∈ rowCases590, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase590 : ∀ entry ∈ rowCases590, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases591 : List PhysicalCase := []
theorem rowFits591 : ∀ entry ∈ rowCases591, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked591 : ∀ entry ∈ rowCases591, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero591 : ∀ entry ∈ rowCases591, entry.hero = 289 := by exact (by intro entry member; cases member)
theorem rowDirection591 : ∀ entry ∈ rowCases591, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase591 : ∀ entry ∈ rowCases591, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases592 : List PhysicalCase := [case547, case814]
theorem memberCase547 : case547 ∈ rowCases592 := by exact List.mem_cons_self
theorem memberCase814 : case814 ∈ rowCases592 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits592 : ∀ entry ∈ rowCases592, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case547_fitted, (List.forall_mem_cons.mpr ⟨case814_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked592 : ∀ entry ∈ rowCases592, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame547_checked, (List.forall_mem_cons.mpr ⟨frame814_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero592 : ∀ entry ∈ rowCases592, entry.hero = 290 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection592 : ∀ entry ∈ rowCases592, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase592 : ∀ entry ∈ rowCases592, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases593 : List PhysicalCase := []
theorem rowFits593 : ∀ entry ∈ rowCases593, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked593 : ∀ entry ∈ rowCases593, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero593 : ∀ entry ∈ rowCases593, entry.hero = 290 := by exact (by intro entry member; cases member)
theorem rowDirection593 : ∀ entry ∈ rowCases593, entry.direction = .south := by exact (by intro entry member; cases member)
theorem rowPhase593 : ∀ entry ∈ rowCases593, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases594 : List PhysicalCase := [case548, case832]
theorem memberCase548 : case548 ∈ rowCases594 := by exact List.mem_cons_self
theorem memberCase832 : case832 ∈ rowCases594 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits594 : ∀ entry ∈ rowCases594, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case548_fitted, (List.forall_mem_cons.mpr ⟨case832_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked594 : ∀ entry ∈ rowCases594, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame548_checked, (List.forall_mem_cons.mpr ⟨frame832_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero594 : ∀ entry ∈ rowCases594, entry.hero = 290 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection594 : ∀ entry ∈ rowCases594, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase594 : ∀ entry ∈ rowCases594, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases595 : List PhysicalCase := [case549, case827]
theorem memberCase549 : case549 ∈ rowCases595 := by exact List.mem_cons_self
theorem memberCase827 : case827 ∈ rowCases595 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits595 : ∀ entry ∈ rowCases595, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case549_fitted, (List.forall_mem_cons.mpr ⟨case827_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked595 : ∀ entry ∈ rowCases595, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame549_checked, (List.forall_mem_cons.mpr ⟨frame827_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero595 : ∀ entry ∈ rowCases595, entry.hero = 290 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection595 : ∀ entry ∈ rowCases595, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase595 : ∀ entry ∈ rowCases595, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases596 : List PhysicalCase := [case550, case551]
theorem memberCase550 : case550 ∈ rowCases596 := by exact List.mem_cons_self
theorem memberCase551 : case551 ∈ rowCases596 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits596 : ∀ entry ∈ rowCases596, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case550_fitted, (List.forall_mem_cons.mpr ⟨case551_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked596 : ∀ entry ∈ rowCases596, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame550_checked, (List.forall_mem_cons.mpr ⟨frame551_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero596 : ∀ entry ∈ rowCases596, entry.hero = 290 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection596 : ∀ entry ∈ rowCases596, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase596 : ∀ entry ∈ rowCases596, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases597 : List PhysicalCase := [case552, case553]
theorem memberCase552 : case552 ∈ rowCases597 := by exact List.mem_cons_self
theorem memberCase553 : case553 ∈ rowCases597 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits597 : ∀ entry ∈ rowCases597, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case552_fitted, (List.forall_mem_cons.mpr ⟨case553_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked597 : ∀ entry ∈ rowCases597, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame552_checked, (List.forall_mem_cons.mpr ⟨frame553_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero597 : ∀ entry ∈ rowCases597, entry.hero = 290 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection597 : ∀ entry ∈ rowCases597, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase597 : ∀ entry ∈ rowCases597, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases598 : List PhysicalCase := [case554]
theorem memberCase554 : case554 ∈ rowCases598 := by exact List.mem_cons_self
theorem rowFits598 : ∀ entry ∈ rowCases598, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case554_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked598 : ∀ entry ∈ rowCases598, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame554_checked, (by intro entry member; cases member)⟩)
theorem rowHero598 : ∀ entry ∈ rowCases598, entry.hero = 290 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection598 : ∀ entry ∈ rowCases598, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase598 : ∀ entry ∈ rowCases598, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases599 : List PhysicalCase := []
theorem rowFits599 : ∀ entry ∈ rowCases599, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked599 : ∀ entry ∈ rowCases599, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero599 : ∀ entry ∈ rowCases599, entry.hero = 290 := by exact (by intro entry member; cases member)
theorem rowDirection599 : ∀ entry ∈ rowCases599, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase599 : ∀ entry ∈ rowCases599, entry.phase = 4 := by exact (by intro entry member; cases member)
end NetHack.Soko12Forward220.Unified.P04
