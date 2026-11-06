import NetHack.Soko12Forward220.Unified.P02.OracleCases12
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P02
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
noncomputable def rowCases650 : List PhysicalCase := [case604]
theorem memberCase604 : case604 ∈ rowCases650 := by exact List.mem_cons_self
theorem rowFits650 : ∀ entry ∈ rowCases650, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case604_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked650 : ∀ entry ∈ rowCases650, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame604_checked, (by intro entry member; cases member)⟩)
theorem rowHero650 : ∀ entry ∈ rowCases650, entry.hero = 319 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection650 : ∀ entry ∈ rowCases650, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase650 : ∀ entry ∈ rowCases650, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases651 : List PhysicalCase := [case605, case837]
theorem memberCase605 : case605 ∈ rowCases651 := by exact List.mem_cons_self
theorem memberCase837 : case837 ∈ rowCases651 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits651 : ∀ entry ∈ rowCases651, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case605_fitted, (List.forall_mem_cons.mpr ⟨case837_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked651 : ∀ entry ∈ rowCases651, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame605_checked, (List.forall_mem_cons.mpr ⟨frame837_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero651 : ∀ entry ∈ rowCases651, entry.hero = 319 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection651 : ∀ entry ∈ rowCases651, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase651 : ∀ entry ∈ rowCases651, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases652 : List PhysicalCase := [case606, case607]
theorem memberCase606 : case606 ∈ rowCases652 := by exact List.mem_cons_self
theorem memberCase607 : case607 ∈ rowCases652 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits652 : ∀ entry ∈ rowCases652, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case606_fitted, (List.forall_mem_cons.mpr ⟨case607_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked652 : ∀ entry ∈ rowCases652, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame606_checked, (List.forall_mem_cons.mpr ⟨frame607_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero652 : ∀ entry ∈ rowCases652, entry.hero = 319 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection652 : ∀ entry ∈ rowCases652, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase652 : ∀ entry ∈ rowCases652, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases653 : List PhysicalCase := [case608, case609]
theorem memberCase608 : case608 ∈ rowCases653 := by exact List.mem_cons_self
theorem memberCase609 : case609 ∈ rowCases653 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits653 : ∀ entry ∈ rowCases653, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case608_fitted, (List.forall_mem_cons.mpr ⟨case609_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked653 : ∀ entry ∈ rowCases653, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame608_checked, (List.forall_mem_cons.mpr ⟨frame609_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero653 : ∀ entry ∈ rowCases653, entry.hero = 319 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection653 : ∀ entry ∈ rowCases653, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase653 : ∀ entry ∈ rowCases653, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases654 : List PhysicalCase := []
theorem rowFits654 : ∀ entry ∈ rowCases654, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked654 : ∀ entry ∈ rowCases654, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero654 : ∀ entry ∈ rowCases654, entry.hero = 319 := by exact (by intro entry member; cases member)
theorem rowDirection654 : ∀ entry ∈ rowCases654, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase654 : ∀ entry ∈ rowCases654, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases655 : List PhysicalCase := []
theorem rowFits655 : ∀ entry ∈ rowCases655, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked655 : ∀ entry ∈ rowCases655, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero655 : ∀ entry ∈ rowCases655, entry.hero = 319 := by exact (by intro entry member; cases member)
theorem rowDirection655 : ∀ entry ∈ rowCases655, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase655 : ∀ entry ∈ rowCases655, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases656 : List PhysicalCase := [case610]
theorem memberCase610 : case610 ∈ rowCases656 := by exact List.mem_cons_self
theorem rowFits656 : ∀ entry ∈ rowCases656, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case610_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked656 : ∀ entry ∈ rowCases656, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame610_checked, (by intro entry member; cases member)⟩)
theorem rowHero656 : ∀ entry ∈ rowCases656, entry.hero = 320 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection656 : ∀ entry ∈ rowCases656, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase656 : ∀ entry ∈ rowCases656, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases657 : List PhysicalCase := []
theorem rowFits657 : ∀ entry ∈ rowCases657, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked657 : ∀ entry ∈ rowCases657, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero657 : ∀ entry ∈ rowCases657, entry.hero = 320 := by exact (by intro entry member; cases member)
theorem rowDirection657 : ∀ entry ∈ rowCases657, entry.direction = .south := by exact (by intro entry member; cases member)
theorem rowPhase657 : ∀ entry ∈ rowCases657, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases658 : List PhysicalCase := []
theorem rowFits658 : ∀ entry ∈ rowCases658, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked658 : ∀ entry ∈ rowCases658, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero658 : ∀ entry ∈ rowCases658, entry.hero = 320 := by exact (by intro entry member; cases member)
theorem rowDirection658 : ∀ entry ∈ rowCases658, entry.direction = .east := by exact (by intro entry member; cases member)
theorem rowPhase658 : ∀ entry ∈ rowCases658, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases659 : List PhysicalCase := [case611, case841]
theorem memberCase611 : case611 ∈ rowCases659 := by exact List.mem_cons_self
theorem memberCase841 : case841 ∈ rowCases659 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits659 : ∀ entry ∈ rowCases659, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case611_fitted, (List.forall_mem_cons.mpr ⟨case841_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked659 : ∀ entry ∈ rowCases659, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame611_checked, (List.forall_mem_cons.mpr ⟨frame841_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero659 : ∀ entry ∈ rowCases659, entry.hero = 320 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection659 : ∀ entry ∈ rowCases659, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase659 : ∀ entry ∈ rowCases659, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases660 : List PhysicalCase := []
theorem rowFits660 : ∀ entry ∈ rowCases660, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked660 : ∀ entry ∈ rowCases660, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero660 : ∀ entry ∈ rowCases660, entry.hero = 320 := by exact (by intro entry member; cases member)
theorem rowDirection660 : ∀ entry ∈ rowCases660, entry.direction = .northEast := by exact (by intro entry member; cases member)
theorem rowPhase660 : ∀ entry ∈ rowCases660, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases661 : List PhysicalCase := [case612, case613]
theorem memberCase612 : case612 ∈ rowCases661 := by exact List.mem_cons_self
theorem memberCase613 : case613 ∈ rowCases661 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits661 : ∀ entry ∈ rowCases661, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case612_fitted, (List.forall_mem_cons.mpr ⟨case613_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked661 : ∀ entry ∈ rowCases661, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame612_checked, (List.forall_mem_cons.mpr ⟨frame613_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero661 : ∀ entry ∈ rowCases661, entry.hero = 320 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection661 : ∀ entry ∈ rowCases661, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase661 : ∀ entry ∈ rowCases661, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases662 : List PhysicalCase := []
theorem rowFits662 : ∀ entry ∈ rowCases662, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked662 : ∀ entry ∈ rowCases662, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero662 : ∀ entry ∈ rowCases662, entry.hero = 320 := by exact (by intro entry member; cases member)
theorem rowDirection662 : ∀ entry ∈ rowCases662, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase662 : ∀ entry ∈ rowCases662, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases663 : List PhysicalCase := [case614]
theorem memberCase614 : case614 ∈ rowCases663 := by exact List.mem_cons_self
theorem rowFits663 : ∀ entry ∈ rowCases663, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case614_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked663 : ∀ entry ∈ rowCases663, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame614_checked, (by intro entry member; cases member)⟩)
theorem rowHero663 : ∀ entry ∈ rowCases663, entry.hero = 320 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection663 : ∀ entry ∈ rowCases663, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase663 : ∀ entry ∈ rowCases663, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases664 : List PhysicalCase := [case615, case834]
theorem memberCase615 : case615 ∈ rowCases664 := by exact List.mem_cons_self
theorem memberCase834 : case834 ∈ rowCases664 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits664 : ∀ entry ∈ rowCases664, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case615_fitted, (List.forall_mem_cons.mpr ⟨case834_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked664 : ∀ entry ∈ rowCases664, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame615_checked, (List.forall_mem_cons.mpr ⟨frame834_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero664 : ∀ entry ∈ rowCases664, entry.hero = 322 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection664 : ∀ entry ∈ rowCases664, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase664 : ∀ entry ∈ rowCases664, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases665 : List PhysicalCase := [case616, case847]
theorem memberCase616 : case616 ∈ rowCases665 := by exact List.mem_cons_self
theorem memberCase847 : case847 ∈ rowCases665 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits665 : ∀ entry ∈ rowCases665, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case616_fitted, (List.forall_mem_cons.mpr ⟨case847_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked665 : ∀ entry ∈ rowCases665, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame616_checked, (List.forall_mem_cons.mpr ⟨frame847_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero665 : ∀ entry ∈ rowCases665, entry.hero = 322 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection665 : ∀ entry ∈ rowCases665, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase665 : ∀ entry ∈ rowCases665, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases666 : List PhysicalCase := []
theorem rowFits666 : ∀ entry ∈ rowCases666, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked666 : ∀ entry ∈ rowCases666, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero666 : ∀ entry ∈ rowCases666, entry.hero = 322 := by exact (by intro entry member; cases member)
theorem rowDirection666 : ∀ entry ∈ rowCases666, entry.direction = .east := by exact (by intro entry member; cases member)
theorem rowPhase666 : ∀ entry ∈ rowCases666, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases667 : List PhysicalCase := []
theorem rowFits667 : ∀ entry ∈ rowCases667, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked667 : ∀ entry ∈ rowCases667, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero667 : ∀ entry ∈ rowCases667, entry.hero = 322 := by exact (by intro entry member; cases member)
theorem rowDirection667 : ∀ entry ∈ rowCases667, entry.direction = .west := by exact (by intro entry member; cases member)
theorem rowPhase667 : ∀ entry ∈ rowCases667, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases668 : List PhysicalCase := [case617]
theorem memberCase617 : case617 ∈ rowCases668 := by exact List.mem_cons_self
theorem rowFits668 : ∀ entry ∈ rowCases668, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case617_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked668 : ∀ entry ∈ rowCases668, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame617_checked, (by intro entry member; cases member)⟩)
theorem rowHero668 : ∀ entry ∈ rowCases668, entry.hero = 322 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection668 : ∀ entry ∈ rowCases668, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase668 : ∀ entry ∈ rowCases668, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases669 : List PhysicalCase := []
theorem rowFits669 : ∀ entry ∈ rowCases669, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked669 : ∀ entry ∈ rowCases669, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero669 : ∀ entry ∈ rowCases669, entry.hero = 322 := by exact (by intro entry member; cases member)
theorem rowDirection669 : ∀ entry ∈ rowCases669, entry.direction = .northWest := by exact (by intro entry member; cases member)
theorem rowPhase669 : ∀ entry ∈ rowCases669, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases670 : List PhysicalCase := []
theorem rowFits670 : ∀ entry ∈ rowCases670, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked670 : ∀ entry ∈ rowCases670, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero670 : ∀ entry ∈ rowCases670, entry.hero = 322 := by exact (by intro entry member; cases member)
theorem rowDirection670 : ∀ entry ∈ rowCases670, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase670 : ∀ entry ∈ rowCases670, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases671 : List PhysicalCase := []
theorem rowFits671 : ∀ entry ∈ rowCases671, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked671 : ∀ entry ∈ rowCases671, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero671 : ∀ entry ∈ rowCases671, entry.hero = 322 := by exact (by intro entry member; cases member)
theorem rowDirection671 : ∀ entry ∈ rowCases671, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase671 : ∀ entry ∈ rowCases671, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases672 : List PhysicalCase := [case618, case838]
theorem memberCase618 : case618 ∈ rowCases672 := by exact List.mem_cons_self
theorem memberCase838 : case838 ∈ rowCases672 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits672 : ∀ entry ∈ rowCases672, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case618_fitted, (List.forall_mem_cons.mpr ⟨case838_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked672 : ∀ entry ∈ rowCases672, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame618_checked, (List.forall_mem_cons.mpr ⟨frame838_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero672 : ∀ entry ∈ rowCases672, entry.hero = 345 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection672 : ∀ entry ∈ rowCases672, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase672 : ∀ entry ∈ rowCases672, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases673 : List PhysicalCase := [case619, case849]
theorem memberCase619 : case619 ∈ rowCases673 := by exact List.mem_cons_self
theorem memberCase849 : case849 ∈ rowCases673 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits673 : ∀ entry ∈ rowCases673, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case619_fitted, (List.forall_mem_cons.mpr ⟨case849_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked673 : ∀ entry ∈ rowCases673, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame619_checked, (List.forall_mem_cons.mpr ⟨frame849_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero673 : ∀ entry ∈ rowCases673, entry.hero = 345 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection673 : ∀ entry ∈ rowCases673, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase673 : ∀ entry ∈ rowCases673, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases674 : List PhysicalCase := []
theorem rowFits674 : ∀ entry ∈ rowCases674, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked674 : ∀ entry ∈ rowCases674, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero674 : ∀ entry ∈ rowCases674, entry.hero = 345 := by exact (by intro entry member; cases member)
theorem rowDirection674 : ∀ entry ∈ rowCases674, entry.direction = .east := by exact (by intro entry member; cases member)
theorem rowPhase674 : ∀ entry ∈ rowCases674, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases675 : List PhysicalCase := []
theorem rowFits675 : ∀ entry ∈ rowCases675, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked675 : ∀ entry ∈ rowCases675, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero675 : ∀ entry ∈ rowCases675, entry.hero = 345 := by exact (by intro entry member; cases member)
theorem rowDirection675 : ∀ entry ∈ rowCases675, entry.direction = .west := by exact (by intro entry member; cases member)
theorem rowPhase675 : ∀ entry ∈ rowCases675, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases676 : List PhysicalCase := [case620]
theorem memberCase620 : case620 ∈ rowCases676 := by exact List.mem_cons_self
theorem rowFits676 : ∀ entry ∈ rowCases676, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case620_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked676 : ∀ entry ∈ rowCases676, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame620_checked, (by intro entry member; cases member)⟩)
theorem rowHero676 : ∀ entry ∈ rowCases676, entry.hero = 345 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection676 : ∀ entry ∈ rowCases676, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase676 : ∀ entry ∈ rowCases676, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases677 : List PhysicalCase := [case621]
theorem memberCase621 : case621 ∈ rowCases677 := by exact List.mem_cons_self
theorem rowFits677 : ∀ entry ∈ rowCases677, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case621_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked677 : ∀ entry ∈ rowCases677, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame621_checked, (by intro entry member; cases member)⟩)
theorem rowHero677 : ∀ entry ∈ rowCases677, entry.hero = 345 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection677 : ∀ entry ∈ rowCases677, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase677 : ∀ entry ∈ rowCases677, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases678 : List PhysicalCase := [case622]
theorem memberCase622 : case622 ∈ rowCases678 := by exact List.mem_cons_self
theorem rowFits678 : ∀ entry ∈ rowCases678, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case622_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked678 : ∀ entry ∈ rowCases678, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame622_checked, (by intro entry member; cases member)⟩)
theorem rowHero678 : ∀ entry ∈ rowCases678, entry.hero = 345 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection678 : ∀ entry ∈ rowCases678, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase678 : ∀ entry ∈ rowCases678, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases679 : List PhysicalCase := [case623]
theorem memberCase623 : case623 ∈ rowCases679 := by exact List.mem_cons_self
theorem rowFits679 : ∀ entry ∈ rowCases679, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case623_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked679 : ∀ entry ∈ rowCases679, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame623_checked, (by intro entry member; cases member)⟩)
theorem rowHero679 : ∀ entry ∈ rowCases679, entry.hero = 345 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection679 : ∀ entry ∈ rowCases679, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase679 : ∀ entry ∈ rowCases679, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases680 : List PhysicalCase := [case624, case842]
theorem memberCase624 : case624 ∈ rowCases680 := by exact List.mem_cons_self
theorem memberCase842 : case842 ∈ rowCases680 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits680 : ∀ entry ∈ rowCases680, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case624_fitted, (List.forall_mem_cons.mpr ⟨case842_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked680 : ∀ entry ∈ rowCases680, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame624_checked, (List.forall_mem_cons.mpr ⟨frame842_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero680 : ∀ entry ∈ rowCases680, entry.hero = 348 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection680 : ∀ entry ∈ rowCases680, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase680 : ∀ entry ∈ rowCases680, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases681 : List PhysicalCase := [case625, case857]
theorem memberCase625 : case625 ∈ rowCases681 := by exact List.mem_cons_self
theorem memberCase857 : case857 ∈ rowCases681 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits681 : ∀ entry ∈ rowCases681, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case625_fitted, (List.forall_mem_cons.mpr ⟨case857_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked681 : ∀ entry ∈ rowCases681, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame625_checked, (List.forall_mem_cons.mpr ⟨frame857_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero681 : ∀ entry ∈ rowCases681, entry.hero = 348 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection681 : ∀ entry ∈ rowCases681, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase681 : ∀ entry ∈ rowCases681, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases682 : List PhysicalCase := []
theorem rowFits682 : ∀ entry ∈ rowCases682, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked682 : ∀ entry ∈ rowCases682, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero682 : ∀ entry ∈ rowCases682, entry.hero = 348 := by exact (by intro entry member; cases member)
theorem rowDirection682 : ∀ entry ∈ rowCases682, entry.direction = .east := by exact (by intro entry member; cases member)
theorem rowPhase682 : ∀ entry ∈ rowCases682, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases683 : List PhysicalCase := []
theorem rowFits683 : ∀ entry ∈ rowCases683, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked683 : ∀ entry ∈ rowCases683, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero683 : ∀ entry ∈ rowCases683, entry.hero = 348 := by exact (by intro entry member; cases member)
theorem rowDirection683 : ∀ entry ∈ rowCases683, entry.direction = .west := by exact (by intro entry member; cases member)
theorem rowPhase683 : ∀ entry ∈ rowCases683, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases684 : List PhysicalCase := []
theorem rowFits684 : ∀ entry ∈ rowCases684, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked684 : ∀ entry ∈ rowCases684, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero684 : ∀ entry ∈ rowCases684, entry.hero = 348 := by exact (by intro entry member; cases member)
theorem rowDirection684 : ∀ entry ∈ rowCases684, entry.direction = .northEast := by exact (by intro entry member; cases member)
theorem rowPhase684 : ∀ entry ∈ rowCases684, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases685 : List PhysicalCase := []
theorem rowFits685 : ∀ entry ∈ rowCases685, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked685 : ∀ entry ∈ rowCases685, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero685 : ∀ entry ∈ rowCases685, entry.hero = 348 := by exact (by intro entry member; cases member)
theorem rowDirection685 : ∀ entry ∈ rowCases685, entry.direction = .northWest := by exact (by intro entry member; cases member)
theorem rowPhase685 : ∀ entry ∈ rowCases685, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases686 : List PhysicalCase := []
theorem rowFits686 : ∀ entry ∈ rowCases686, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked686 : ∀ entry ∈ rowCases686, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero686 : ∀ entry ∈ rowCases686, entry.hero = 348 := by exact (by intro entry member; cases member)
theorem rowDirection686 : ∀ entry ∈ rowCases686, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase686 : ∀ entry ∈ rowCases686, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases687 : List PhysicalCase := [case626]
theorem memberCase626 : case626 ∈ rowCases687 := by exact List.mem_cons_self
theorem rowFits687 : ∀ entry ∈ rowCases687, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case626_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked687 : ∀ entry ∈ rowCases687, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame626_checked, (by intro entry member; cases member)⟩)
theorem rowHero687 : ∀ entry ∈ rowCases687, entry.hero = 348 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection687 : ∀ entry ∈ rowCases687, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase687 : ∀ entry ∈ rowCases687, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases688 : List PhysicalCase := []
theorem rowFits688 : ∀ entry ∈ rowCases688, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked688 : ∀ entry ∈ rowCases688, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero688 : ∀ entry ∈ rowCases688, entry.hero = 370 := by exact (by intro entry member; cases member)
theorem rowDirection688 : ∀ entry ∈ rowCases688, entry.direction = .north := by exact (by intro entry member; cases member)
theorem rowPhase688 : ∀ entry ∈ rowCases688, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases689 : List PhysicalCase := [case627]
theorem memberCase627 : case627 ∈ rowCases689 := by exact List.mem_cons_self
theorem rowFits689 : ∀ entry ∈ rowCases689, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case627_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked689 : ∀ entry ∈ rowCases689, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame627_checked, (by intro entry member; cases member)⟩)
theorem rowHero689 : ∀ entry ∈ rowCases689, entry.hero = 370 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection689 : ∀ entry ∈ rowCases689, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase689 : ∀ entry ∈ rowCases689, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases690 : List PhysicalCase := [case628, case850]
theorem memberCase628 : case628 ∈ rowCases690 := by exact List.mem_cons_self
theorem memberCase850 : case850 ∈ rowCases690 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits690 : ∀ entry ∈ rowCases690, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case628_fitted, (List.forall_mem_cons.mpr ⟨case850_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked690 : ∀ entry ∈ rowCases690, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame628_checked, (List.forall_mem_cons.mpr ⟨frame850_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero690 : ∀ entry ∈ rowCases690, entry.hero = 370 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection690 : ∀ entry ∈ rowCases690, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase690 : ∀ entry ∈ rowCases690, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases691 : List PhysicalCase := []
theorem rowFits691 : ∀ entry ∈ rowCases691, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked691 : ∀ entry ∈ rowCases691, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero691 : ∀ entry ∈ rowCases691, entry.hero = 370 := by exact (by intro entry member; cases member)
theorem rowDirection691 : ∀ entry ∈ rowCases691, entry.direction = .west := by exact (by intro entry member; cases member)
theorem rowPhase691 : ∀ entry ∈ rowCases691, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases692 : List PhysicalCase := [case629]
theorem memberCase629 : case629 ∈ rowCases692 := by exact List.mem_cons_self
theorem rowFits692 : ∀ entry ∈ rowCases692, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case629_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked692 : ∀ entry ∈ rowCases692, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame629_checked, (by intro entry member; cases member)⟩)
theorem rowHero692 : ∀ entry ∈ rowCases692, entry.hero = 370 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection692 : ∀ entry ∈ rowCases692, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase692 : ∀ entry ∈ rowCases692, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases693 : List PhysicalCase := []
theorem rowFits693 : ∀ entry ∈ rowCases693, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked693 : ∀ entry ∈ rowCases693, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero693 : ∀ entry ∈ rowCases693, entry.hero = 370 := by exact (by intro entry member; cases member)
theorem rowDirection693 : ∀ entry ∈ rowCases693, entry.direction = .northWest := by exact (by intro entry member; cases member)
theorem rowPhase693 : ∀ entry ∈ rowCases693, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases694 : List PhysicalCase := [case630]
theorem memberCase630 : case630 ∈ rowCases694 := by exact List.mem_cons_self
theorem rowFits694 : ∀ entry ∈ rowCases694, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case630_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked694 : ∀ entry ∈ rowCases694, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame630_checked, (by intro entry member; cases member)⟩)
theorem rowHero694 : ∀ entry ∈ rowCases694, entry.hero = 370 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection694 : ∀ entry ∈ rowCases694, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase694 : ∀ entry ∈ rowCases694, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases695 : List PhysicalCase := []
theorem rowFits695 : ∀ entry ∈ rowCases695, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked695 : ∀ entry ∈ rowCases695, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero695 : ∀ entry ∈ rowCases695, entry.hero = 370 := by exact (by intro entry member; cases member)
theorem rowDirection695 : ∀ entry ∈ rowCases695, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase695 : ∀ entry ∈ rowCases695, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases696 : List PhysicalCase := [case631, case844]
theorem memberCase631 : case631 ∈ rowCases696 := by exact List.mem_cons_self
theorem memberCase844 : case844 ∈ rowCases696 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits696 : ∀ entry ∈ rowCases696, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case631_fitted, (List.forall_mem_cons.mpr ⟨case844_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked696 : ∀ entry ∈ rowCases696, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame631_checked, (List.forall_mem_cons.mpr ⟨frame844_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero696 : ∀ entry ∈ rowCases696, entry.hero = 371 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection696 : ∀ entry ∈ rowCases696, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase696 : ∀ entry ∈ rowCases696, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases697 : List PhysicalCase := [case632]
theorem memberCase632 : case632 ∈ rowCases697 := by exact List.mem_cons_self
theorem rowFits697 : ∀ entry ∈ rowCases697, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case632_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked697 : ∀ entry ∈ rowCases697, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame632_checked, (by intro entry member; cases member)⟩)
theorem rowHero697 : ∀ entry ∈ rowCases697, entry.hero = 371 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection697 : ∀ entry ∈ rowCases697, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase697 : ∀ entry ∈ rowCases697, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases698 : List PhysicalCase := [case633, case852]
theorem memberCase633 : case633 ∈ rowCases698 := by exact List.mem_cons_self
theorem memberCase852 : case852 ∈ rowCases698 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits698 : ∀ entry ∈ rowCases698, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case633_fitted, (List.forall_mem_cons.mpr ⟨case852_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked698 : ∀ entry ∈ rowCases698, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame633_checked, (List.forall_mem_cons.mpr ⟨frame852_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero698 : ∀ entry ∈ rowCases698, entry.hero = 371 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection698 : ∀ entry ∈ rowCases698, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase698 : ∀ entry ∈ rowCases698, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases699 : List PhysicalCase := [case634]
theorem memberCase634 : case634 ∈ rowCases699 := by exact List.mem_cons_self
theorem rowFits699 : ∀ entry ∈ rowCases699, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case634_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked699 : ∀ entry ∈ rowCases699, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame634_checked, (by intro entry member; cases member)⟩)
theorem rowHero699 : ∀ entry ∈ rowCases699, entry.hero = 371 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection699 : ∀ entry ∈ rowCases699, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase699 : ∀ entry ∈ rowCases699, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
end NetHack.Soko12Forward220.Unified.P02
