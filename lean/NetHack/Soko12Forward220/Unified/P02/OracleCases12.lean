import NetHack.Soko12Forward220.Unified.P02.OracleCases11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P02
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
noncomputable def rowCases600 : List PhysicalCase := []
theorem rowFits600 : ∀ entry ∈ rowCases600, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked600 : ∀ entry ∈ rowCases600, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero600 : ∀ entry ∈ rowCases600, entry.hero = 293 := by exact (by intro entry member; cases member)
theorem rowDirection600 : ∀ entry ∈ rowCases600, entry.direction = .north := by exact (by intro entry member; cases member)
theorem rowPhase600 : ∀ entry ∈ rowCases600, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases601 : List PhysicalCase := [case567, case839]
theorem memberCase567 : case567 ∈ rowCases601 := by exact List.mem_cons_self
theorem memberCase839 : case839 ∈ rowCases601 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits601 : ∀ entry ∈ rowCases601, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case567_fitted, (List.forall_mem_cons.mpr ⟨case839_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked601 : ∀ entry ∈ rowCases601, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame567_checked, (List.forall_mem_cons.mpr ⟨frame839_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero601 : ∀ entry ∈ rowCases601, entry.hero = 293 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection601 : ∀ entry ∈ rowCases601, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase601 : ∀ entry ∈ rowCases601, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases602 : List PhysicalCase := [case568]
theorem memberCase568 : case568 ∈ rowCases602 := by exact List.mem_cons_self
theorem rowFits602 : ∀ entry ∈ rowCases602, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case568_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked602 : ∀ entry ∈ rowCases602, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame568_checked, (by intro entry member; cases member)⟩)
theorem rowHero602 : ∀ entry ∈ rowCases602, entry.hero = 293 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection602 : ∀ entry ∈ rowCases602, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase602 : ∀ entry ∈ rowCases602, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases603 : List PhysicalCase := [case569, case831]
theorem memberCase569 : case569 ∈ rowCases603 := by exact List.mem_cons_self
theorem memberCase831 : case831 ∈ rowCases603 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits603 : ∀ entry ∈ rowCases603, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case569_fitted, (List.forall_mem_cons.mpr ⟨case831_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked603 : ∀ entry ∈ rowCases603, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame569_checked, (List.forall_mem_cons.mpr ⟨frame831_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero603 : ∀ entry ∈ rowCases603, entry.hero = 293 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection603 : ∀ entry ∈ rowCases603, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase603 : ∀ entry ∈ rowCases603, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases604 : List PhysicalCase := []
theorem rowFits604 : ∀ entry ∈ rowCases604, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked604 : ∀ entry ∈ rowCases604, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero604 : ∀ entry ∈ rowCases604, entry.hero = 293 := by exact (by intro entry member; cases member)
theorem rowDirection604 : ∀ entry ∈ rowCases604, entry.direction = .northEast := by exact (by intro entry member; cases member)
theorem rowPhase604 : ∀ entry ∈ rowCases604, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases605 : List PhysicalCase := []
theorem rowFits605 : ∀ entry ∈ rowCases605, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked605 : ∀ entry ∈ rowCases605, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero605 : ∀ entry ∈ rowCases605, entry.hero = 293 := by exact (by intro entry member; cases member)
theorem rowDirection605 : ∀ entry ∈ rowCases605, entry.direction = .northWest := by exact (by intro entry member; cases member)
theorem rowPhase605 : ∀ entry ∈ rowCases605, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases606 : List PhysicalCase := [case570, case571]
theorem memberCase570 : case570 ∈ rowCases606 := by exact List.mem_cons_self
theorem memberCase571 : case571 ∈ rowCases606 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits606 : ∀ entry ∈ rowCases606, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case570_fitted, (List.forall_mem_cons.mpr ⟨case571_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked606 : ∀ entry ∈ rowCases606, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame570_checked, (List.forall_mem_cons.mpr ⟨frame571_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero606 : ∀ entry ∈ rowCases606, entry.hero = 293 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection606 : ∀ entry ∈ rowCases606, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase606 : ∀ entry ∈ rowCases606, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases607 : List PhysicalCase := [case572, case573]
theorem memberCase572 : case572 ∈ rowCases607 := by exact List.mem_cons_self
theorem memberCase573 : case573 ∈ rowCases607 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits607 : ∀ entry ∈ rowCases607, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case572_fitted, (List.forall_mem_cons.mpr ⟨case573_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked607 : ∀ entry ∈ rowCases607, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame572_checked, (List.forall_mem_cons.mpr ⟨frame573_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero607 : ∀ entry ∈ rowCases607, entry.hero = 293 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection607 : ∀ entry ∈ rowCases607, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase607 : ∀ entry ∈ rowCases607, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases608 : List PhysicalCase := []
theorem rowFits608 : ∀ entry ∈ rowCases608, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked608 : ∀ entry ∈ rowCases608, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero608 : ∀ entry ∈ rowCases608, entry.hero = 294 := by exact (by intro entry member; cases member)
theorem rowDirection608 : ∀ entry ∈ rowCases608, entry.direction = .north := by exact (by intro entry member; cases member)
theorem rowPhase608 : ∀ entry ∈ rowCases608, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases609 : List PhysicalCase := [case574]
theorem memberCase574 : case574 ∈ rowCases609 := by exact List.mem_cons_self
theorem rowFits609 : ∀ entry ∈ rowCases609, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case574_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked609 : ∀ entry ∈ rowCases609, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame574_checked, (by intro entry member; cases member)⟩)
theorem rowHero609 : ∀ entry ∈ rowCases609, entry.hero = 294 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection609 : ∀ entry ∈ rowCases609, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase609 : ∀ entry ∈ rowCases609, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases610 : List PhysicalCase := []
theorem rowFits610 : ∀ entry ∈ rowCases610, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked610 : ∀ entry ∈ rowCases610, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero610 : ∀ entry ∈ rowCases610, entry.hero = 294 := by exact (by intro entry member; cases member)
theorem rowDirection610 : ∀ entry ∈ rowCases610, entry.direction = .east := by exact (by intro entry member; cases member)
theorem rowPhase610 : ∀ entry ∈ rowCases610, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases611 : List PhysicalCase := [case575, case833]
theorem memberCase575 : case575 ∈ rowCases611 := by exact List.mem_cons_self
theorem memberCase833 : case833 ∈ rowCases611 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits611 : ∀ entry ∈ rowCases611, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case575_fitted, (List.forall_mem_cons.mpr ⟨case833_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked611 : ∀ entry ∈ rowCases611, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame575_checked, (List.forall_mem_cons.mpr ⟨frame833_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero611 : ∀ entry ∈ rowCases611, entry.hero = 294 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection611 : ∀ entry ∈ rowCases611, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase611 : ∀ entry ∈ rowCases611, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases612 : List PhysicalCase := []
theorem rowFits612 : ∀ entry ∈ rowCases612, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked612 : ∀ entry ∈ rowCases612, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero612 : ∀ entry ∈ rowCases612, entry.hero = 294 := by exact (by intro entry member; cases member)
theorem rowDirection612 : ∀ entry ∈ rowCases612, entry.direction = .northEast := by exact (by intro entry member; cases member)
theorem rowPhase612 : ∀ entry ∈ rowCases612, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases613 : List PhysicalCase := []
theorem rowFits613 : ∀ entry ∈ rowCases613, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked613 : ∀ entry ∈ rowCases613, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero613 : ∀ entry ∈ rowCases613, entry.hero = 294 := by exact (by intro entry member; cases member)
theorem rowDirection613 : ∀ entry ∈ rowCases613, entry.direction = .northWest := by exact (by intro entry member; cases member)
theorem rowPhase613 : ∀ entry ∈ rowCases613, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases614 : List PhysicalCase := []
theorem rowFits614 : ∀ entry ∈ rowCases614, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked614 : ∀ entry ∈ rowCases614, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero614 : ∀ entry ∈ rowCases614, entry.hero = 294 := by exact (by intro entry member; cases member)
theorem rowDirection614 : ∀ entry ∈ rowCases614, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase614 : ∀ entry ∈ rowCases614, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases615 : List PhysicalCase := [case576, case577]
theorem memberCase576 : case576 ∈ rowCases615 := by exact List.mem_cons_self
theorem memberCase577 : case577 ∈ rowCases615 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits615 : ∀ entry ∈ rowCases615, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case576_fitted, (List.forall_mem_cons.mpr ⟨case577_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked615 : ∀ entry ∈ rowCases615, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame576_checked, (List.forall_mem_cons.mpr ⟨frame577_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero615 : ∀ entry ∈ rowCases615, entry.hero = 294 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection615 : ∀ entry ∈ rowCases615, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase615 : ∀ entry ∈ rowCases615, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases616 : List PhysicalCase := [case578, case816]
theorem memberCase578 : case578 ∈ rowCases616 := by exact List.mem_cons_self
theorem memberCase816 : case816 ∈ rowCases616 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits616 : ∀ entry ∈ rowCases616, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case578_fitted, (List.forall_mem_cons.mpr ⟨case816_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked616 : ∀ entry ∈ rowCases616, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame578_checked, (List.forall_mem_cons.mpr ⟨frame816_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero616 : ∀ entry ∈ rowCases616, entry.hero = 296 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection616 : ∀ entry ∈ rowCases616, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase616 : ∀ entry ∈ rowCases616, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases617 : List PhysicalCase := [case579, case843]
theorem memberCase579 : case579 ∈ rowCases617 := by exact List.mem_cons_self
theorem memberCase843 : case843 ∈ rowCases617 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits617 : ∀ entry ∈ rowCases617, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case579_fitted, (List.forall_mem_cons.mpr ⟨case843_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked617 : ∀ entry ∈ rowCases617, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame579_checked, (List.forall_mem_cons.mpr ⟨frame843_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero617 : ∀ entry ∈ rowCases617, entry.hero = 296 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection617 : ∀ entry ∈ rowCases617, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase617 : ∀ entry ∈ rowCases617, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases618 : List PhysicalCase := [case580]
theorem memberCase580 : case580 ∈ rowCases618 := by exact List.mem_cons_self
theorem rowFits618 : ∀ entry ∈ rowCases618, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case580_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked618 : ∀ entry ∈ rowCases618, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame580_checked, (by intro entry member; cases member)⟩)
theorem rowHero618 : ∀ entry ∈ rowCases618, entry.hero = 296 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection618 : ∀ entry ∈ rowCases618, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase618 : ∀ entry ∈ rowCases618, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases619 : List PhysicalCase := []
theorem rowFits619 : ∀ entry ∈ rowCases619, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked619 : ∀ entry ∈ rowCases619, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero619 : ∀ entry ∈ rowCases619, entry.hero = 296 := by exact (by intro entry member; cases member)
theorem rowDirection619 : ∀ entry ∈ rowCases619, entry.direction = .west := by exact (by intro entry member; cases member)
theorem rowPhase619 : ∀ entry ∈ rowCases619, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases620 : List PhysicalCase := [case581, case582]
theorem memberCase581 : case581 ∈ rowCases620 := by exact List.mem_cons_self
theorem memberCase582 : case582 ∈ rowCases620 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits620 : ∀ entry ∈ rowCases620, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case581_fitted, (List.forall_mem_cons.mpr ⟨case582_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked620 : ∀ entry ∈ rowCases620, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame581_checked, (List.forall_mem_cons.mpr ⟨frame582_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero620 : ∀ entry ∈ rowCases620, entry.hero = 296 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection620 : ∀ entry ∈ rowCases620, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase620 : ∀ entry ∈ rowCases620, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases621 : List PhysicalCase := []
theorem rowFits621 : ∀ entry ∈ rowCases621, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked621 : ∀ entry ∈ rowCases621, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero621 : ∀ entry ∈ rowCases621, entry.hero = 296 := by exact (by intro entry member; cases member)
theorem rowDirection621 : ∀ entry ∈ rowCases621, entry.direction = .northWest := by exact (by intro entry member; cases member)
theorem rowPhase621 : ∀ entry ∈ rowCases621, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases622 : List PhysicalCase := []
theorem rowFits622 : ∀ entry ∈ rowCases622, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked622 : ∀ entry ∈ rowCases622, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero622 : ∀ entry ∈ rowCases622, entry.hero = 296 := by exact (by intro entry member; cases member)
theorem rowDirection622 : ∀ entry ∈ rowCases622, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase622 : ∀ entry ∈ rowCases622, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases623 : List PhysicalCase := []
theorem rowFits623 : ∀ entry ∈ rowCases623, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked623 : ∀ entry ∈ rowCases623, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero623 : ∀ entry ∈ rowCases623, entry.hero = 296 := by exact (by intro entry member; cases member)
theorem rowDirection623 : ∀ entry ∈ rowCases623, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase623 : ∀ entry ∈ rowCases623, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases624 : List PhysicalCase := [case583, case818]
theorem memberCase583 : case583 ∈ rowCases624 := by exact List.mem_cons_self
theorem memberCase818 : case818 ∈ rowCases624 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits624 : ∀ entry ∈ rowCases624, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case583_fitted, (List.forall_mem_cons.mpr ⟨case818_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked624 : ∀ entry ∈ rowCases624, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame583_checked, (List.forall_mem_cons.mpr ⟨frame818_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero624 : ∀ entry ∈ rowCases624, entry.hero = 297 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection624 : ∀ entry ∈ rowCases624, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase624 : ∀ entry ∈ rowCases624, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases625 : List PhysicalCase := []
theorem rowFits625 : ∀ entry ∈ rowCases625, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked625 : ∀ entry ∈ rowCases625, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero625 : ∀ entry ∈ rowCases625, entry.hero = 297 := by exact (by intro entry member; cases member)
theorem rowDirection625 : ∀ entry ∈ rowCases625, entry.direction = .south := by exact (by intro entry member; cases member)
theorem rowPhase625 : ∀ entry ∈ rowCases625, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases626 : List PhysicalCase := []
theorem rowFits626 : ∀ entry ∈ rowCases626, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked626 : ∀ entry ∈ rowCases626, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero626 : ∀ entry ∈ rowCases626, entry.hero = 297 := by exact (by intro entry member; cases member)
theorem rowDirection626 : ∀ entry ∈ rowCases626, entry.direction = .east := by exact (by intro entry member; cases member)
theorem rowPhase626 : ∀ entry ∈ rowCases626, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases627 : List PhysicalCase := [case584]
theorem memberCase584 : case584 ∈ rowCases627 := by exact List.mem_cons_self
theorem rowFits627 : ∀ entry ∈ rowCases627, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case584_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked627 : ∀ entry ∈ rowCases627, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame584_checked, (by intro entry member; cases member)⟩)
theorem rowHero627 : ∀ entry ∈ rowCases627, entry.hero = 297 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection627 : ∀ entry ∈ rowCases627, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase627 : ∀ entry ∈ rowCases627, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases628 : List PhysicalCase := [case585]
theorem memberCase585 : case585 ∈ rowCases628 := by exact List.mem_cons_self
theorem rowFits628 : ∀ entry ∈ rowCases628, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case585_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked628 : ∀ entry ∈ rowCases628, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame585_checked, (by intro entry member; cases member)⟩)
theorem rowHero628 : ∀ entry ∈ rowCases628, entry.hero = 297 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection628 : ∀ entry ∈ rowCases628, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase628 : ∀ entry ∈ rowCases628, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases629 : List PhysicalCase := [case586, case587]
theorem memberCase586 : case586 ∈ rowCases629 := by exact List.mem_cons_self
theorem memberCase587 : case587 ∈ rowCases629 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits629 : ∀ entry ∈ rowCases629, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case586_fitted, (List.forall_mem_cons.mpr ⟨case587_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked629 : ∀ entry ∈ rowCases629, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame586_checked, (List.forall_mem_cons.mpr ⟨frame587_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero629 : ∀ entry ∈ rowCases629, entry.hero = 297 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection629 : ∀ entry ∈ rowCases629, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase629 : ∀ entry ∈ rowCases629, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases630 : List PhysicalCase := []
theorem rowFits630 : ∀ entry ∈ rowCases630, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked630 : ∀ entry ∈ rowCases630, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero630 : ∀ entry ∈ rowCases630, entry.hero = 297 := by exact (by intro entry member; cases member)
theorem rowDirection630 : ∀ entry ∈ rowCases630, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase630 : ∀ entry ∈ rowCases630, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases631 : List PhysicalCase := [case588]
theorem memberCase588 : case588 ∈ rowCases631 := by exact List.mem_cons_self
theorem rowFits631 : ∀ entry ∈ rowCases631, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case588_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked631 : ∀ entry ∈ rowCases631, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame588_checked, (by intro entry member; cases member)⟩)
theorem rowHero631 : ∀ entry ∈ rowCases631, entry.hero = 297 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection631 : ∀ entry ∈ rowCases631, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase631 : ∀ entry ∈ rowCases631, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases632 : List PhysicalCase := [case589, case826]
theorem memberCase589 : case589 ∈ rowCases632 := by exact List.mem_cons_self
theorem memberCase826 : case826 ∈ rowCases632 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits632 : ∀ entry ∈ rowCases632, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case589_fitted, (List.forall_mem_cons.mpr ⟨case826_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked632 : ∀ entry ∈ rowCases632, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame589_checked, (List.forall_mem_cons.mpr ⟨frame826_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero632 : ∀ entry ∈ rowCases632, entry.hero = 317 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection632 : ∀ entry ∈ rowCases632, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase632 : ∀ entry ∈ rowCases632, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases633 : List PhysicalCase := []
theorem rowFits633 : ∀ entry ∈ rowCases633, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked633 : ∀ entry ∈ rowCases633, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero633 : ∀ entry ∈ rowCases633, entry.hero = 317 := by exact (by intro entry member; cases member)
theorem rowDirection633 : ∀ entry ∈ rowCases633, entry.direction = .south := by exact (by intro entry member; cases member)
theorem rowPhase633 : ∀ entry ∈ rowCases633, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases634 : List PhysicalCase := [case590, case836]
theorem memberCase590 : case590 ∈ rowCases634 := by exact List.mem_cons_self
theorem memberCase836 : case836 ∈ rowCases634 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits634 : ∀ entry ∈ rowCases634, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case590_fitted, (List.forall_mem_cons.mpr ⟨case836_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked634 : ∀ entry ∈ rowCases634, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame590_checked, (List.forall_mem_cons.mpr ⟨frame836_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero634 : ∀ entry ∈ rowCases634, entry.hero = 317 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection634 : ∀ entry ∈ rowCases634, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase634 : ∀ entry ∈ rowCases634, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases635 : List PhysicalCase := []
theorem rowFits635 : ∀ entry ∈ rowCases635, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked635 : ∀ entry ∈ rowCases635, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero635 : ∀ entry ∈ rowCases635, entry.hero = 317 := by exact (by intro entry member; cases member)
theorem rowDirection635 : ∀ entry ∈ rowCases635, entry.direction = .west := by exact (by intro entry member; cases member)
theorem rowPhase635 : ∀ entry ∈ rowCases635, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases636 : List PhysicalCase := [case591, case592]
theorem memberCase591 : case591 ∈ rowCases636 := by exact List.mem_cons_self
theorem memberCase592 : case592 ∈ rowCases636 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits636 : ∀ entry ∈ rowCases636, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case591_fitted, (List.forall_mem_cons.mpr ⟨case592_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked636 : ∀ entry ∈ rowCases636, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame591_checked, (List.forall_mem_cons.mpr ⟨frame592_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero636 : ∀ entry ∈ rowCases636, entry.hero = 317 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection636 : ∀ entry ∈ rowCases636, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase636 : ∀ entry ∈ rowCases636, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases637 : List PhysicalCase := [case593]
theorem memberCase593 : case593 ∈ rowCases637 := by exact List.mem_cons_self
theorem rowFits637 : ∀ entry ∈ rowCases637, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case593_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked637 : ∀ entry ∈ rowCases637, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame593_checked, (by intro entry member; cases member)⟩)
theorem rowHero637 : ∀ entry ∈ rowCases637, entry.hero = 317 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection637 : ∀ entry ∈ rowCases637, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase637 : ∀ entry ∈ rowCases637, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases638 : List PhysicalCase := []
theorem rowFits638 : ∀ entry ∈ rowCases638, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked638 : ∀ entry ∈ rowCases638, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero638 : ∀ entry ∈ rowCases638, entry.hero = 317 := by exact (by intro entry member; cases member)
theorem rowDirection638 : ∀ entry ∈ rowCases638, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase638 : ∀ entry ∈ rowCases638, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases639 : List PhysicalCase := []
theorem rowFits639 : ∀ entry ∈ rowCases639, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked639 : ∀ entry ∈ rowCases639, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero639 : ∀ entry ∈ rowCases639, entry.hero = 317 := by exact (by intro entry member; cases member)
theorem rowDirection639 : ∀ entry ∈ rowCases639, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase639 : ∀ entry ∈ rowCases639, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases640 : List PhysicalCase := [case594]
theorem memberCase594 : case594 ∈ rowCases640 := by exact List.mem_cons_self
theorem rowFits640 : ∀ entry ∈ rowCases640, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case594_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked640 : ∀ entry ∈ rowCases640, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame594_checked, (by intro entry member; cases member)⟩)
theorem rowHero640 : ∀ entry ∈ rowCases640, entry.hero = 318 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection640 : ∀ entry ∈ rowCases640, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase640 : ∀ entry ∈ rowCases640, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases641 : List PhysicalCase := []
theorem rowFits641 : ∀ entry ∈ rowCases641, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked641 : ∀ entry ∈ rowCases641, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero641 : ∀ entry ∈ rowCases641, entry.hero = 318 := by exact (by intro entry member; cases member)
theorem rowDirection641 : ∀ entry ∈ rowCases641, entry.direction = .south := by exact (by intro entry member; cases member)
theorem rowPhase641 : ∀ entry ∈ rowCases641, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases642 : List PhysicalCase := [case595, case840]
theorem memberCase595 : case595 ∈ rowCases642 := by exact List.mem_cons_self
theorem memberCase840 : case840 ∈ rowCases642 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits642 : ∀ entry ∈ rowCases642, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case595_fitted, (List.forall_mem_cons.mpr ⟨case840_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked642 : ∀ entry ∈ rowCases642, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame595_checked, (List.forall_mem_cons.mpr ⟨frame840_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero642 : ∀ entry ∈ rowCases642, entry.hero = 318 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection642 : ∀ entry ∈ rowCases642, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase642 : ∀ entry ∈ rowCases642, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases643 : List PhysicalCase := [case596]
theorem memberCase596 : case596 ∈ rowCases643 := by exact List.mem_cons_self
theorem rowFits643 : ∀ entry ∈ rowCases643, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case596_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked643 : ∀ entry ∈ rowCases643, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame596_checked, (by intro entry member; cases member)⟩)
theorem rowHero643 : ∀ entry ∈ rowCases643, entry.hero = 318 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection643 : ∀ entry ∈ rowCases643, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase643 : ∀ entry ∈ rowCases643, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases644 : List PhysicalCase := [case597, case598]
theorem memberCase597 : case597 ∈ rowCases644 := by exact List.mem_cons_self
theorem memberCase598 : case598 ∈ rowCases644 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits644 : ∀ entry ∈ rowCases644, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case597_fitted, (List.forall_mem_cons.mpr ⟨case598_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked644 : ∀ entry ∈ rowCases644, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame597_checked, (List.forall_mem_cons.mpr ⟨frame598_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero644 : ∀ entry ∈ rowCases644, entry.hero = 318 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection644 : ∀ entry ∈ rowCases644, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase644 : ∀ entry ∈ rowCases644, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases645 : List PhysicalCase := [case599, case600]
theorem memberCase599 : case599 ∈ rowCases645 := by exact List.mem_cons_self
theorem memberCase600 : case600 ∈ rowCases645 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits645 : ∀ entry ∈ rowCases645, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case599_fitted, (List.forall_mem_cons.mpr ⟨case600_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked645 : ∀ entry ∈ rowCases645, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame599_checked, (List.forall_mem_cons.mpr ⟨frame600_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero645 : ∀ entry ∈ rowCases645, entry.hero = 318 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection645 : ∀ entry ∈ rowCases645, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase645 : ∀ entry ∈ rowCases645, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases646 : List PhysicalCase := [case601]
theorem memberCase601 : case601 ∈ rowCases646 := by exact List.mem_cons_self
theorem rowFits646 : ∀ entry ∈ rowCases646, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case601_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked646 : ∀ entry ∈ rowCases646, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame601_checked, (by intro entry member; cases member)⟩)
theorem rowHero646 : ∀ entry ∈ rowCases646, entry.hero = 318 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection646 : ∀ entry ∈ rowCases646, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase646 : ∀ entry ∈ rowCases646, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases647 : List PhysicalCase := []
theorem rowFits647 : ∀ entry ∈ rowCases647, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked647 : ∀ entry ∈ rowCases647, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero647 : ∀ entry ∈ rowCases647, entry.hero = 318 := by exact (by intro entry member; cases member)
theorem rowDirection647 : ∀ entry ∈ rowCases647, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase647 : ∀ entry ∈ rowCases647, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases648 : List PhysicalCase := [case602]
theorem memberCase602 : case602 ∈ rowCases648 := by exact List.mem_cons_self
theorem rowFits648 : ∀ entry ∈ rowCases648, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case602_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked648 : ∀ entry ∈ rowCases648, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame602_checked, (by intro entry member; cases member)⟩)
theorem rowHero648 : ∀ entry ∈ rowCases648, entry.hero = 319 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection648 : ∀ entry ∈ rowCases648, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase648 : ∀ entry ∈ rowCases648, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases649 : List PhysicalCase := [case603, case845]
theorem memberCase603 : case603 ∈ rowCases649 := by exact List.mem_cons_self
theorem memberCase845 : case845 ∈ rowCases649 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits649 : ∀ entry ∈ rowCases649, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case603_fitted, (List.forall_mem_cons.mpr ⟨case845_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked649 : ∀ entry ∈ rowCases649, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame603_checked, (List.forall_mem_cons.mpr ⟨frame845_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero649 : ∀ entry ∈ rowCases649, entry.hero = 319 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection649 : ∀ entry ∈ rowCases649, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase649 : ∀ entry ∈ rowCases649, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
end NetHack.Soko12Forward220.Unified.P02
