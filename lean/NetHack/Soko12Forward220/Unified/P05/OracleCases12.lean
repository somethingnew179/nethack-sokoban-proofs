import NetHack.Soko12Forward220.Unified.P05.OracleCases11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P05
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
noncomputable def rowCases600 : List PhysicalCase := [case549, case816]
theorem memberCase549 : case549 ∈ rowCases600 := by exact List.mem_cons_self
theorem memberCase816 : case816 ∈ rowCases600 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits600 : ∀ entry ∈ rowCases600, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case549_fitted, (List.forall_mem_cons.mpr ⟨case816_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked600 : ∀ entry ∈ rowCases600, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame549_checked, (List.forall_mem_cons.mpr ⟨frame816_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero600 : ∀ entry ∈ rowCases600, entry.hero = 290 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection600 : ∀ entry ∈ rowCases600, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase600 : ∀ entry ∈ rowCases600, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases601 : List PhysicalCase := []
theorem rowFits601 : ∀ entry ∈ rowCases601, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked601 : ∀ entry ∈ rowCases601, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero601 : ∀ entry ∈ rowCases601, entry.hero = 290 := by exact (by intro entry member; cases member)
theorem rowDirection601 : ∀ entry ∈ rowCases601, entry.direction = .south := by exact (by intro entry member; cases member)
theorem rowPhase601 : ∀ entry ∈ rowCases601, entry.phase = 5 := by exact (by intro entry member; cases member)
noncomputable def rowCases602 : List PhysicalCase := [case550, case834]
theorem memberCase550 : case550 ∈ rowCases602 := by exact List.mem_cons_self
theorem memberCase834 : case834 ∈ rowCases602 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits602 : ∀ entry ∈ rowCases602, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case550_fitted, (List.forall_mem_cons.mpr ⟨case834_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked602 : ∀ entry ∈ rowCases602, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame550_checked, (List.forall_mem_cons.mpr ⟨frame834_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero602 : ∀ entry ∈ rowCases602, entry.hero = 290 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection602 : ∀ entry ∈ rowCases602, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase602 : ∀ entry ∈ rowCases602, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases603 : List PhysicalCase := [case551, case829]
theorem memberCase551 : case551 ∈ rowCases603 := by exact List.mem_cons_self
theorem memberCase829 : case829 ∈ rowCases603 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits603 : ∀ entry ∈ rowCases603, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case551_fitted, (List.forall_mem_cons.mpr ⟨case829_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked603 : ∀ entry ∈ rowCases603, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame551_checked, (List.forall_mem_cons.mpr ⟨frame829_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero603 : ∀ entry ∈ rowCases603, entry.hero = 290 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection603 : ∀ entry ∈ rowCases603, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase603 : ∀ entry ∈ rowCases603, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases604 : List PhysicalCase := [case552, case553]
theorem memberCase552 : case552 ∈ rowCases604 := by exact List.mem_cons_self
theorem memberCase553 : case553 ∈ rowCases604 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits604 : ∀ entry ∈ rowCases604, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case552_fitted, (List.forall_mem_cons.mpr ⟨case553_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked604 : ∀ entry ∈ rowCases604, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame552_checked, (List.forall_mem_cons.mpr ⟨frame553_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero604 : ∀ entry ∈ rowCases604, entry.hero = 290 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection604 : ∀ entry ∈ rowCases604, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase604 : ∀ entry ∈ rowCases604, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases605 : List PhysicalCase := [case554, case555]
theorem memberCase554 : case554 ∈ rowCases605 := by exact List.mem_cons_self
theorem memberCase555 : case555 ∈ rowCases605 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits605 : ∀ entry ∈ rowCases605, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case554_fitted, (List.forall_mem_cons.mpr ⟨case555_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked605 : ∀ entry ∈ rowCases605, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame554_checked, (List.forall_mem_cons.mpr ⟨frame555_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero605 : ∀ entry ∈ rowCases605, entry.hero = 290 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection605 : ∀ entry ∈ rowCases605, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase605 : ∀ entry ∈ rowCases605, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases606 : List PhysicalCase := [case556]
theorem memberCase556 : case556 ∈ rowCases606 := by exact List.mem_cons_self
theorem rowFits606 : ∀ entry ∈ rowCases606, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case556_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked606 : ∀ entry ∈ rowCases606, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame556_checked, (by intro entry member; cases member)⟩)
theorem rowHero606 : ∀ entry ∈ rowCases606, entry.hero = 290 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection606 : ∀ entry ∈ rowCases606, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase606 : ∀ entry ∈ rowCases606, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases607 : List PhysicalCase := []
theorem rowFits607 : ∀ entry ∈ rowCases607, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked607 : ∀ entry ∈ rowCases607, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero607 : ∀ entry ∈ rowCases607, entry.hero = 290 := by exact (by intro entry member; cases member)
theorem rowDirection607 : ∀ entry ∈ rowCases607, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase607 : ∀ entry ∈ rowCases607, entry.phase = 5 := by exact (by intro entry member; cases member)
noncomputable def rowCases608 : List PhysicalCase := [case557, case820]
theorem memberCase557 : case557 ∈ rowCases608 := by exact List.mem_cons_self
theorem memberCase820 : case820 ∈ rowCases608 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits608 : ∀ entry ∈ rowCases608, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case557_fitted, (List.forall_mem_cons.mpr ⟨case820_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked608 : ∀ entry ∈ rowCases608, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame557_checked, (List.forall_mem_cons.mpr ⟨frame820_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero608 : ∀ entry ∈ rowCases608, entry.hero = 291 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection608 : ∀ entry ∈ rowCases608, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase608 : ∀ entry ∈ rowCases608, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases609 : List PhysicalCase := [case558]
theorem memberCase558 : case558 ∈ rowCases609 := by exact List.mem_cons_self
theorem rowFits609 : ∀ entry ∈ rowCases609, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case558_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked609 : ∀ entry ∈ rowCases609, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame558_checked, (by intro entry member; cases member)⟩)
theorem rowHero609 : ∀ entry ∈ rowCases609, entry.hero = 291 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection609 : ∀ entry ∈ rowCases609, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase609 : ∀ entry ∈ rowCases609, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases610 : List PhysicalCase := [case559, case836]
theorem memberCase559 : case559 ∈ rowCases610 := by exact List.mem_cons_self
theorem memberCase836 : case836 ∈ rowCases610 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits610 : ∀ entry ∈ rowCases610, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case559_fitted, (List.forall_mem_cons.mpr ⟨case836_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked610 : ∀ entry ∈ rowCases610, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame559_checked, (List.forall_mem_cons.mpr ⟨frame836_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero610 : ∀ entry ∈ rowCases610, entry.hero = 291 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection610 : ∀ entry ∈ rowCases610, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase610 : ∀ entry ∈ rowCases610, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases611 : List PhysicalCase := [case560, case831]
theorem memberCase560 : case560 ∈ rowCases611 := by exact List.mem_cons_self
theorem memberCase831 : case831 ∈ rowCases611 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits611 : ∀ entry ∈ rowCases611, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case560_fitted, (List.forall_mem_cons.mpr ⟨case831_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked611 : ∀ entry ∈ rowCases611, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame560_checked, (List.forall_mem_cons.mpr ⟨frame831_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero611 : ∀ entry ∈ rowCases611, entry.hero = 291 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection611 : ∀ entry ∈ rowCases611, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase611 : ∀ entry ∈ rowCases611, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases612 : List PhysicalCase := []
theorem rowFits612 : ∀ entry ∈ rowCases612, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked612 : ∀ entry ∈ rowCases612, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero612 : ∀ entry ∈ rowCases612, entry.hero = 291 := by exact (by intro entry member; cases member)
theorem rowDirection612 : ∀ entry ∈ rowCases612, entry.direction = .northEast := by exact (by intro entry member; cases member)
theorem rowPhase612 : ∀ entry ∈ rowCases612, entry.phase = 5 := by exact (by intro entry member; cases member)
noncomputable def rowCases613 : List PhysicalCase := [case561, case562]
theorem memberCase561 : case561 ∈ rowCases613 := by exact List.mem_cons_self
theorem memberCase562 : case562 ∈ rowCases613 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits613 : ∀ entry ∈ rowCases613, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case561_fitted, (List.forall_mem_cons.mpr ⟨case562_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked613 : ∀ entry ∈ rowCases613, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame561_checked, (List.forall_mem_cons.mpr ⟨frame562_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero613 : ∀ entry ∈ rowCases613, entry.hero = 291 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection613 : ∀ entry ∈ rowCases613, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase613 : ∀ entry ∈ rowCases613, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases614 : List PhysicalCase := [case563, case564]
theorem memberCase563 : case563 ∈ rowCases614 := by exact List.mem_cons_self
theorem memberCase564 : case564 ∈ rowCases614 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits614 : ∀ entry ∈ rowCases614, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case563_fitted, (List.forall_mem_cons.mpr ⟨case564_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked614 : ∀ entry ∈ rowCases614, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame563_checked, (List.forall_mem_cons.mpr ⟨frame564_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero614 : ∀ entry ∈ rowCases614, entry.hero = 291 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection614 : ∀ entry ∈ rowCases614, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase614 : ∀ entry ∈ rowCases614, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases615 : List PhysicalCase := []
theorem rowFits615 : ∀ entry ∈ rowCases615, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked615 : ∀ entry ∈ rowCases615, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero615 : ∀ entry ∈ rowCases615, entry.hero = 291 := by exact (by intro entry member; cases member)
theorem rowDirection615 : ∀ entry ∈ rowCases615, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase615 : ∀ entry ∈ rowCases615, entry.phase = 5 := by exact (by intro entry member; cases member)
noncomputable def rowCases616 : List PhysicalCase := []
theorem rowFits616 : ∀ entry ∈ rowCases616, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked616 : ∀ entry ∈ rowCases616, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero616 : ∀ entry ∈ rowCases616, entry.hero = 292 := by exact (by intro entry member; cases member)
theorem rowDirection616 : ∀ entry ∈ rowCases616, entry.direction = .north := by exact (by intro entry member; cases member)
theorem rowPhase616 : ∀ entry ∈ rowCases616, entry.phase = 5 := by exact (by intro entry member; cases member)
noncomputable def rowCases617 : List PhysicalCase := [case565]
theorem memberCase565 : case565 ∈ rowCases617 := by exact List.mem_cons_self
theorem rowFits617 : ∀ entry ∈ rowCases617, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case565_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked617 : ∀ entry ∈ rowCases617, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame565_checked, (by intro entry member; cases member)⟩)
theorem rowHero617 : ∀ entry ∈ rowCases617, entry.hero = 292 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection617 : ∀ entry ∈ rowCases617, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase617 : ∀ entry ∈ rowCases617, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases618 : List PhysicalCase := [case566, case838]
theorem memberCase566 : case566 ∈ rowCases618 := by exact List.mem_cons_self
theorem memberCase838 : case838 ∈ rowCases618 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits618 : ∀ entry ∈ rowCases618, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case566_fitted, (List.forall_mem_cons.mpr ⟨case838_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked618 : ∀ entry ∈ rowCases618, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame566_checked, (List.forall_mem_cons.mpr ⟨frame838_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero618 : ∀ entry ∈ rowCases618, entry.hero = 292 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection618 : ∀ entry ∈ rowCases618, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase618 : ∀ entry ∈ rowCases618, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases619 : List PhysicalCase := [case567, case835]
theorem memberCase567 : case567 ∈ rowCases619 := by exact List.mem_cons_self
theorem memberCase835 : case835 ∈ rowCases619 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits619 : ∀ entry ∈ rowCases619, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case567_fitted, (List.forall_mem_cons.mpr ⟨case835_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked619 : ∀ entry ∈ rowCases619, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame567_checked, (List.forall_mem_cons.mpr ⟨frame835_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero619 : ∀ entry ∈ rowCases619, entry.hero = 292 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection619 : ∀ entry ∈ rowCases619, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase619 : ∀ entry ∈ rowCases619, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases620 : List PhysicalCase := []
theorem rowFits620 : ∀ entry ∈ rowCases620, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked620 : ∀ entry ∈ rowCases620, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero620 : ∀ entry ∈ rowCases620, entry.hero = 292 := by exact (by intro entry member; cases member)
theorem rowDirection620 : ∀ entry ∈ rowCases620, entry.direction = .northEast := by exact (by intro entry member; cases member)
theorem rowPhase620 : ∀ entry ∈ rowCases620, entry.phase = 5 := by exact (by intro entry member; cases member)
noncomputable def rowCases621 : List PhysicalCase := [case568]
theorem memberCase568 : case568 ∈ rowCases621 := by exact List.mem_cons_self
theorem rowFits621 : ∀ entry ∈ rowCases621, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case568_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked621 : ∀ entry ∈ rowCases621, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame568_checked, (by intro entry member; cases member)⟩)
theorem rowHero621 : ∀ entry ∈ rowCases621, entry.hero = 292 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection621 : ∀ entry ∈ rowCases621, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase621 : ∀ entry ∈ rowCases621, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases622 : List PhysicalCase := [case569, case570]
theorem memberCase569 : case569 ∈ rowCases622 := by exact List.mem_cons_self
theorem memberCase570 : case570 ∈ rowCases622 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits622 : ∀ entry ∈ rowCases622, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case569_fitted, (List.forall_mem_cons.mpr ⟨case570_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked622 : ∀ entry ∈ rowCases622, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame569_checked, (List.forall_mem_cons.mpr ⟨frame570_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero622 : ∀ entry ∈ rowCases622, entry.hero = 292 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection622 : ∀ entry ∈ rowCases622, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase622 : ∀ entry ∈ rowCases622, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases623 : List PhysicalCase := [case571, case572]
theorem memberCase571 : case571 ∈ rowCases623 := by exact List.mem_cons_self
theorem memberCase572 : case572 ∈ rowCases623 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits623 : ∀ entry ∈ rowCases623, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case571_fitted, (List.forall_mem_cons.mpr ⟨case572_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked623 : ∀ entry ∈ rowCases623, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame571_checked, (List.forall_mem_cons.mpr ⟨frame572_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero623 : ∀ entry ∈ rowCases623, entry.hero = 292 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection623 : ∀ entry ∈ rowCases623, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase623 : ∀ entry ∈ rowCases623, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases624 : List PhysicalCase := []
theorem rowFits624 : ∀ entry ∈ rowCases624, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked624 : ∀ entry ∈ rowCases624, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero624 : ∀ entry ∈ rowCases624, entry.hero = 293 := by exact (by intro entry member; cases member)
theorem rowDirection624 : ∀ entry ∈ rowCases624, entry.direction = .north := by exact (by intro entry member; cases member)
theorem rowPhase624 : ∀ entry ∈ rowCases624, entry.phase = 5 := by exact (by intro entry member; cases member)
noncomputable def rowCases625 : List PhysicalCase := [case573, case845]
theorem memberCase573 : case573 ∈ rowCases625 := by exact List.mem_cons_self
theorem memberCase845 : case845 ∈ rowCases625 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits625 : ∀ entry ∈ rowCases625, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case573_fitted, (List.forall_mem_cons.mpr ⟨case845_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked625 : ∀ entry ∈ rowCases625, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame573_checked, (List.forall_mem_cons.mpr ⟨frame845_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero625 : ∀ entry ∈ rowCases625, entry.hero = 293 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection625 : ∀ entry ∈ rowCases625, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase625 : ∀ entry ∈ rowCases625, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases626 : List PhysicalCase := [case574]
theorem memberCase574 : case574 ∈ rowCases626 := by exact List.mem_cons_self
theorem rowFits626 : ∀ entry ∈ rowCases626, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case574_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked626 : ∀ entry ∈ rowCases626, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame574_checked, (by intro entry member; cases member)⟩)
theorem rowHero626 : ∀ entry ∈ rowCases626, entry.hero = 293 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection626 : ∀ entry ∈ rowCases626, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase626 : ∀ entry ∈ rowCases626, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases627 : List PhysicalCase := [case575, case837]
theorem memberCase575 : case575 ∈ rowCases627 := by exact List.mem_cons_self
theorem memberCase837 : case837 ∈ rowCases627 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits627 : ∀ entry ∈ rowCases627, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case575_fitted, (List.forall_mem_cons.mpr ⟨case837_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked627 : ∀ entry ∈ rowCases627, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame575_checked, (List.forall_mem_cons.mpr ⟨frame837_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero627 : ∀ entry ∈ rowCases627, entry.hero = 293 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection627 : ∀ entry ∈ rowCases627, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase627 : ∀ entry ∈ rowCases627, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases628 : List PhysicalCase := []
theorem rowFits628 : ∀ entry ∈ rowCases628, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked628 : ∀ entry ∈ rowCases628, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero628 : ∀ entry ∈ rowCases628, entry.hero = 293 := by exact (by intro entry member; cases member)
theorem rowDirection628 : ∀ entry ∈ rowCases628, entry.direction = .northEast := by exact (by intro entry member; cases member)
theorem rowPhase628 : ∀ entry ∈ rowCases628, entry.phase = 5 := by exact (by intro entry member; cases member)
noncomputable def rowCases629 : List PhysicalCase := []
theorem rowFits629 : ∀ entry ∈ rowCases629, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked629 : ∀ entry ∈ rowCases629, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero629 : ∀ entry ∈ rowCases629, entry.hero = 293 := by exact (by intro entry member; cases member)
theorem rowDirection629 : ∀ entry ∈ rowCases629, entry.direction = .northWest := by exact (by intro entry member; cases member)
theorem rowPhase629 : ∀ entry ∈ rowCases629, entry.phase = 5 := by exact (by intro entry member; cases member)
noncomputable def rowCases630 : List PhysicalCase := [case576, case577]
theorem memberCase576 : case576 ∈ rowCases630 := by exact List.mem_cons_self
theorem memberCase577 : case577 ∈ rowCases630 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits630 : ∀ entry ∈ rowCases630, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case576_fitted, (List.forall_mem_cons.mpr ⟨case577_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked630 : ∀ entry ∈ rowCases630, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame576_checked, (List.forall_mem_cons.mpr ⟨frame577_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero630 : ∀ entry ∈ rowCases630, entry.hero = 293 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection630 : ∀ entry ∈ rowCases630, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase630 : ∀ entry ∈ rowCases630, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases631 : List PhysicalCase := [case578, case579]
theorem memberCase578 : case578 ∈ rowCases631 := by exact List.mem_cons_self
theorem memberCase579 : case579 ∈ rowCases631 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits631 : ∀ entry ∈ rowCases631, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case578_fitted, (List.forall_mem_cons.mpr ⟨case579_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked631 : ∀ entry ∈ rowCases631, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame578_checked, (List.forall_mem_cons.mpr ⟨frame579_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero631 : ∀ entry ∈ rowCases631, entry.hero = 293 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection631 : ∀ entry ∈ rowCases631, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase631 : ∀ entry ∈ rowCases631, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases632 : List PhysicalCase := []
theorem rowFits632 : ∀ entry ∈ rowCases632, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked632 : ∀ entry ∈ rowCases632, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero632 : ∀ entry ∈ rowCases632, entry.hero = 294 := by exact (by intro entry member; cases member)
theorem rowDirection632 : ∀ entry ∈ rowCases632, entry.direction = .north := by exact (by intro entry member; cases member)
theorem rowPhase632 : ∀ entry ∈ rowCases632, entry.phase = 5 := by exact (by intro entry member; cases member)
noncomputable def rowCases633 : List PhysicalCase := [case580]
theorem memberCase580 : case580 ∈ rowCases633 := by exact List.mem_cons_self
theorem rowFits633 : ∀ entry ∈ rowCases633, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case580_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked633 : ∀ entry ∈ rowCases633, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame580_checked, (by intro entry member; cases member)⟩)
theorem rowHero633 : ∀ entry ∈ rowCases633, entry.hero = 294 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection633 : ∀ entry ∈ rowCases633, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase633 : ∀ entry ∈ rowCases633, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases634 : List PhysicalCase := []
theorem rowFits634 : ∀ entry ∈ rowCases634, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked634 : ∀ entry ∈ rowCases634, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero634 : ∀ entry ∈ rowCases634, entry.hero = 294 := by exact (by intro entry member; cases member)
theorem rowDirection634 : ∀ entry ∈ rowCases634, entry.direction = .east := by exact (by intro entry member; cases member)
theorem rowPhase634 : ∀ entry ∈ rowCases634, entry.phase = 5 := by exact (by intro entry member; cases member)
noncomputable def rowCases635 : List PhysicalCase := [case581, case839]
theorem memberCase581 : case581 ∈ rowCases635 := by exact List.mem_cons_self
theorem memberCase839 : case839 ∈ rowCases635 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits635 : ∀ entry ∈ rowCases635, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case581_fitted, (List.forall_mem_cons.mpr ⟨case839_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked635 : ∀ entry ∈ rowCases635, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame581_checked, (List.forall_mem_cons.mpr ⟨frame839_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero635 : ∀ entry ∈ rowCases635, entry.hero = 294 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection635 : ∀ entry ∈ rowCases635, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase635 : ∀ entry ∈ rowCases635, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases636 : List PhysicalCase := []
theorem rowFits636 : ∀ entry ∈ rowCases636, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked636 : ∀ entry ∈ rowCases636, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero636 : ∀ entry ∈ rowCases636, entry.hero = 294 := by exact (by intro entry member; cases member)
theorem rowDirection636 : ∀ entry ∈ rowCases636, entry.direction = .northEast := by exact (by intro entry member; cases member)
theorem rowPhase636 : ∀ entry ∈ rowCases636, entry.phase = 5 := by exact (by intro entry member; cases member)
noncomputable def rowCases637 : List PhysicalCase := []
theorem rowFits637 : ∀ entry ∈ rowCases637, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked637 : ∀ entry ∈ rowCases637, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero637 : ∀ entry ∈ rowCases637, entry.hero = 294 := by exact (by intro entry member; cases member)
theorem rowDirection637 : ∀ entry ∈ rowCases637, entry.direction = .northWest := by exact (by intro entry member; cases member)
theorem rowPhase637 : ∀ entry ∈ rowCases637, entry.phase = 5 := by exact (by intro entry member; cases member)
noncomputable def rowCases638 : List PhysicalCase := []
theorem rowFits638 : ∀ entry ∈ rowCases638, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked638 : ∀ entry ∈ rowCases638, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero638 : ∀ entry ∈ rowCases638, entry.hero = 294 := by exact (by intro entry member; cases member)
theorem rowDirection638 : ∀ entry ∈ rowCases638, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase638 : ∀ entry ∈ rowCases638, entry.phase = 5 := by exact (by intro entry member; cases member)
noncomputable def rowCases639 : List PhysicalCase := [case582, case583]
theorem memberCase582 : case582 ∈ rowCases639 := by exact List.mem_cons_self
theorem memberCase583 : case583 ∈ rowCases639 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits639 : ∀ entry ∈ rowCases639, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case582_fitted, (List.forall_mem_cons.mpr ⟨case583_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked639 : ∀ entry ∈ rowCases639, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame582_checked, (List.forall_mem_cons.mpr ⟨frame583_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero639 : ∀ entry ∈ rowCases639, entry.hero = 294 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection639 : ∀ entry ∈ rowCases639, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase639 : ∀ entry ∈ rowCases639, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases640 : List PhysicalCase := [case584, case822]
theorem memberCase584 : case584 ∈ rowCases640 := by exact List.mem_cons_self
theorem memberCase822 : case822 ∈ rowCases640 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits640 : ∀ entry ∈ rowCases640, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case584_fitted, (List.forall_mem_cons.mpr ⟨case822_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked640 : ∀ entry ∈ rowCases640, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame584_checked, (List.forall_mem_cons.mpr ⟨frame822_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero640 : ∀ entry ∈ rowCases640, entry.hero = 296 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection640 : ∀ entry ∈ rowCases640, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase640 : ∀ entry ∈ rowCases640, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases641 : List PhysicalCase := [case585, case849]
theorem memberCase585 : case585 ∈ rowCases641 := by exact List.mem_cons_self
theorem memberCase849 : case849 ∈ rowCases641 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits641 : ∀ entry ∈ rowCases641, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case585_fitted, (List.forall_mem_cons.mpr ⟨case849_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked641 : ∀ entry ∈ rowCases641, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame585_checked, (List.forall_mem_cons.mpr ⟨frame849_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero641 : ∀ entry ∈ rowCases641, entry.hero = 296 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection641 : ∀ entry ∈ rowCases641, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase641 : ∀ entry ∈ rowCases641, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases642 : List PhysicalCase := [case586]
theorem memberCase586 : case586 ∈ rowCases642 := by exact List.mem_cons_self
theorem rowFits642 : ∀ entry ∈ rowCases642, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case586_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked642 : ∀ entry ∈ rowCases642, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame586_checked, (by intro entry member; cases member)⟩)
theorem rowHero642 : ∀ entry ∈ rowCases642, entry.hero = 296 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection642 : ∀ entry ∈ rowCases642, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase642 : ∀ entry ∈ rowCases642, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases643 : List PhysicalCase := []
theorem rowFits643 : ∀ entry ∈ rowCases643, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked643 : ∀ entry ∈ rowCases643, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero643 : ∀ entry ∈ rowCases643, entry.hero = 296 := by exact (by intro entry member; cases member)
theorem rowDirection643 : ∀ entry ∈ rowCases643, entry.direction = .west := by exact (by intro entry member; cases member)
theorem rowPhase643 : ∀ entry ∈ rowCases643, entry.phase = 5 := by exact (by intro entry member; cases member)
noncomputable def rowCases644 : List PhysicalCase := [case587, case588]
theorem memberCase587 : case587 ∈ rowCases644 := by exact List.mem_cons_self
theorem memberCase588 : case588 ∈ rowCases644 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits644 : ∀ entry ∈ rowCases644, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case587_fitted, (List.forall_mem_cons.mpr ⟨case588_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked644 : ∀ entry ∈ rowCases644, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame587_checked, (List.forall_mem_cons.mpr ⟨frame588_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero644 : ∀ entry ∈ rowCases644, entry.hero = 296 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection644 : ∀ entry ∈ rowCases644, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase644 : ∀ entry ∈ rowCases644, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases645 : List PhysicalCase := []
theorem rowFits645 : ∀ entry ∈ rowCases645, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked645 : ∀ entry ∈ rowCases645, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero645 : ∀ entry ∈ rowCases645, entry.hero = 296 := by exact (by intro entry member; cases member)
theorem rowDirection645 : ∀ entry ∈ rowCases645, entry.direction = .northWest := by exact (by intro entry member; cases member)
theorem rowPhase645 : ∀ entry ∈ rowCases645, entry.phase = 5 := by exact (by intro entry member; cases member)
noncomputable def rowCases646 : List PhysicalCase := []
theorem rowFits646 : ∀ entry ∈ rowCases646, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked646 : ∀ entry ∈ rowCases646, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero646 : ∀ entry ∈ rowCases646, entry.hero = 296 := by exact (by intro entry member; cases member)
theorem rowDirection646 : ∀ entry ∈ rowCases646, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase646 : ∀ entry ∈ rowCases646, entry.phase = 5 := by exact (by intro entry member; cases member)
noncomputable def rowCases647 : List PhysicalCase := []
theorem rowFits647 : ∀ entry ∈ rowCases647, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked647 : ∀ entry ∈ rowCases647, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero647 : ∀ entry ∈ rowCases647, entry.hero = 296 := by exact (by intro entry member; cases member)
theorem rowDirection647 : ∀ entry ∈ rowCases647, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase647 : ∀ entry ∈ rowCases647, entry.phase = 5 := by exact (by intro entry member; cases member)
noncomputable def rowCases648 : List PhysicalCase := [case589, case824]
theorem memberCase589 : case589 ∈ rowCases648 := by exact List.mem_cons_self
theorem memberCase824 : case824 ∈ rowCases648 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits648 : ∀ entry ∈ rowCases648, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case589_fitted, (List.forall_mem_cons.mpr ⟨case824_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked648 : ∀ entry ∈ rowCases648, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame589_checked, (List.forall_mem_cons.mpr ⟨frame824_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero648 : ∀ entry ∈ rowCases648, entry.hero = 297 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection648 : ∀ entry ∈ rowCases648, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase648 : ∀ entry ∈ rowCases648, entry.phase = 5 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases649 : List PhysicalCase := []
theorem rowFits649 : ∀ entry ∈ rowCases649, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked649 : ∀ entry ∈ rowCases649, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero649 : ∀ entry ∈ rowCases649, entry.hero = 297 := by exact (by intro entry member; cases member)
theorem rowDirection649 : ∀ entry ∈ rowCases649, entry.direction = .south := by exact (by intro entry member; cases member)
theorem rowPhase649 : ∀ entry ∈ rowCases649, entry.phase = 5 := by exact (by intro entry member; cases member)
end NetHack.Soko12Forward220.Unified.P05
