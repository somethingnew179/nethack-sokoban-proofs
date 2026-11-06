import NetHack.Soko12Forward220.Unified.P02.OracleCases14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P02
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
noncomputable def rowCases750 : List PhysicalCase := []
theorem rowFits750 : ∀ entry ∈ rowCases750, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked750 : ∀ entry ∈ rowCases750, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero750 : ∀ entry ∈ rowCases750, entry.hero = 399 := by exact (by intro entry member; cases member)
theorem rowDirection750 : ∀ entry ∈ rowCases750, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase750 : ∀ entry ∈ rowCases750, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases751 : List PhysicalCase := []
theorem rowFits751 : ∀ entry ∈ rowCases751, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked751 : ∀ entry ∈ rowCases751, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero751 : ∀ entry ∈ rowCases751, entry.hero = 399 := by exact (by intro entry member; cases member)
theorem rowDirection751 : ∀ entry ∈ rowCases751, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase751 : ∀ entry ∈ rowCases751, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases752 : List PhysicalCase := [case665, case856]
theorem memberCase665 : case665 ∈ rowCases752 := by exact List.mem_cons_self
theorem memberCase856 : case856 ∈ rowCases752 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits752 : ∀ entry ∈ rowCases752, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case665_fitted, (List.forall_mem_cons.mpr ⟨case856_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked752 : ∀ entry ∈ rowCases752, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame665_checked, (List.forall_mem_cons.mpr ⟨frame856_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero752 : ∀ entry ∈ rowCases752, entry.hero = 400 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection752 : ∀ entry ∈ rowCases752, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase752 : ∀ entry ∈ rowCases752, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases753 : List PhysicalCase := []
theorem rowFits753 : ∀ entry ∈ rowCases753, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked753 : ∀ entry ∈ rowCases753, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero753 : ∀ entry ∈ rowCases753, entry.hero = 400 := by exact (by intro entry member; cases member)
theorem rowDirection753 : ∀ entry ∈ rowCases753, entry.direction = .south := by exact (by intro entry member; cases member)
theorem rowPhase753 : ∀ entry ∈ rowCases753, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases754 : List PhysicalCase := []
theorem rowFits754 : ∀ entry ∈ rowCases754, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked754 : ∀ entry ∈ rowCases754, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero754 : ∀ entry ∈ rowCases754, entry.hero = 400 := by exact (by intro entry member; cases member)
theorem rowDirection754 : ∀ entry ∈ rowCases754, entry.direction = .east := by exact (by intro entry member; cases member)
theorem rowPhase754 : ∀ entry ∈ rowCases754, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases755 : List PhysicalCase := [case666]
theorem memberCase666 : case666 ∈ rowCases755 := by exact List.mem_cons_self
theorem rowFits755 : ∀ entry ∈ rowCases755, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case666_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked755 : ∀ entry ∈ rowCases755, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame666_checked, (by intro entry member; cases member)⟩)
theorem rowHero755 : ∀ entry ∈ rowCases755, entry.hero = 400 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection755 : ∀ entry ∈ rowCases755, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase755 : ∀ entry ∈ rowCases755, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases756 : List PhysicalCase := []
theorem rowFits756 : ∀ entry ∈ rowCases756, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked756 : ∀ entry ∈ rowCases756, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero756 : ∀ entry ∈ rowCases756, entry.hero = 400 := by exact (by intro entry member; cases member)
theorem rowDirection756 : ∀ entry ∈ rowCases756, entry.direction = .northEast := by exact (by intro entry member; cases member)
theorem rowPhase756 : ∀ entry ∈ rowCases756, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases757 : List PhysicalCase := [case667]
theorem memberCase667 : case667 ∈ rowCases757 := by exact List.mem_cons_self
theorem rowFits757 : ∀ entry ∈ rowCases757, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case667_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked757 : ∀ entry ∈ rowCases757, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame667_checked, (by intro entry member; cases member)⟩)
theorem rowHero757 : ∀ entry ∈ rowCases757, entry.hero = 400 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection757 : ∀ entry ∈ rowCases757, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase757 : ∀ entry ∈ rowCases757, entry.phase = 2 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases758 : List PhysicalCase := []
theorem rowFits758 : ∀ entry ∈ rowCases758, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked758 : ∀ entry ∈ rowCases758, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero758 : ∀ entry ∈ rowCases758, entry.hero = 400 := by exact (by intro entry member; cases member)
theorem rowDirection758 : ∀ entry ∈ rowCases758, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase758 : ∀ entry ∈ rowCases758, entry.phase = 2 := by exact (by intro entry member; cases member)
noncomputable def rowCases759 : List PhysicalCase := []
theorem rowFits759 : ∀ entry ∈ rowCases759, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked759 : ∀ entry ∈ rowCases759, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero759 : ∀ entry ∈ rowCases759, entry.hero = 400 := by exact (by intro entry member; cases member)
theorem rowDirection759 : ∀ entry ∈ rowCases759, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase759 : ∀ entry ∈ rowCases759, entry.phase = 2 := by exact (by intro entry member; cases member)
end NetHack.Soko12Forward220.Unified.P02
