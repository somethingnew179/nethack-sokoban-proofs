import NetHack.Soko12Forward220.Unified.P03.OracleCases14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P03
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
noncomputable def rowCases750 : List PhysicalCase := []
theorem rowFits750 : ∀ entry ∈ rowCases750, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked750 : ∀ entry ∈ rowCases750, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero750 : ∀ entry ∈ rowCases750, entry.hero = 397 := by exact (by intro entry member; cases member)
theorem rowDirection750 : ∀ entry ∈ rowCases750, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase750 : ∀ entry ∈ rowCases750, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases751 : List PhysicalCase := []
theorem rowFits751 : ∀ entry ∈ rowCases751, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked751 : ∀ entry ∈ rowCases751, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero751 : ∀ entry ∈ rowCases751, entry.hero = 397 := by exact (by intro entry member; cases member)
theorem rowDirection751 : ∀ entry ∈ rowCases751, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase751 : ∀ entry ∈ rowCases751, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases752 : List PhysicalCase := [case662]
theorem memberCase662 : case662 ∈ rowCases752 := by exact List.mem_cons_self
theorem rowFits752 : ∀ entry ∈ rowCases752, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case662_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked752 : ∀ entry ∈ rowCases752, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame662_checked, (by intro entry member; cases member)⟩)
theorem rowHero752 : ∀ entry ∈ rowCases752, entry.hero = 399 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection752 : ∀ entry ∈ rowCases752, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase752 : ∀ entry ∈ rowCases752, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases753 : List PhysicalCase := []
theorem rowFits753 : ∀ entry ∈ rowCases753, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked753 : ∀ entry ∈ rowCases753, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero753 : ∀ entry ∈ rowCases753, entry.hero = 399 := by exact (by intro entry member; cases member)
theorem rowDirection753 : ∀ entry ∈ rowCases753, entry.direction = .south := by exact (by intro entry member; cases member)
theorem rowPhase753 : ∀ entry ∈ rowCases753, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases754 : List PhysicalCase := [case663]
theorem memberCase663 : case663 ∈ rowCases754 := by exact List.mem_cons_self
theorem rowFits754 : ∀ entry ∈ rowCases754, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case663_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked754 : ∀ entry ∈ rowCases754, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame663_checked, (by intro entry member; cases member)⟩)
theorem rowHero754 : ∀ entry ∈ rowCases754, entry.hero = 399 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection754 : ∀ entry ∈ rowCases754, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase754 : ∀ entry ∈ rowCases754, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases755 : List PhysicalCase := []
theorem rowFits755 : ∀ entry ∈ rowCases755, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked755 : ∀ entry ∈ rowCases755, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero755 : ∀ entry ∈ rowCases755, entry.hero = 399 := by exact (by intro entry member; cases member)
theorem rowDirection755 : ∀ entry ∈ rowCases755, entry.direction = .west := by exact (by intro entry member; cases member)
theorem rowPhase755 : ∀ entry ∈ rowCases755, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases756 : List PhysicalCase := [case664, case665]
theorem memberCase664 : case664 ∈ rowCases756 := by exact List.mem_cons_self
theorem memberCase665 : case665 ∈ rowCases756 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits756 : ∀ entry ∈ rowCases756, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case664_fitted, (List.forall_mem_cons.mpr ⟨case665_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked756 : ∀ entry ∈ rowCases756, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame664_checked, (List.forall_mem_cons.mpr ⟨frame665_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero756 : ∀ entry ∈ rowCases756, entry.hero = 399 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection756 : ∀ entry ∈ rowCases756, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase756 : ∀ entry ∈ rowCases756, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases757 : List PhysicalCase := [case666]
theorem memberCase666 : case666 ∈ rowCases757 := by exact List.mem_cons_self
theorem rowFits757 : ∀ entry ∈ rowCases757, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case666_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked757 : ∀ entry ∈ rowCases757, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame666_checked, (by intro entry member; cases member)⟩)
theorem rowHero757 : ∀ entry ∈ rowCases757, entry.hero = 399 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection757 : ∀ entry ∈ rowCases757, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase757 : ∀ entry ∈ rowCases757, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases758 : List PhysicalCase := []
theorem rowFits758 : ∀ entry ∈ rowCases758, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked758 : ∀ entry ∈ rowCases758, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero758 : ∀ entry ∈ rowCases758, entry.hero = 399 := by exact (by intro entry member; cases member)
theorem rowDirection758 : ∀ entry ∈ rowCases758, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase758 : ∀ entry ∈ rowCases758, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases759 : List PhysicalCase := []
theorem rowFits759 : ∀ entry ∈ rowCases759, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked759 : ∀ entry ∈ rowCases759, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero759 : ∀ entry ∈ rowCases759, entry.hero = 399 := by exact (by intro entry member; cases member)
theorem rowDirection759 : ∀ entry ∈ rowCases759, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase759 : ∀ entry ∈ rowCases759, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases760 : List PhysicalCase := [case667, case858]
theorem memberCase667 : case667 ∈ rowCases760 := by exact List.mem_cons_self
theorem memberCase858 : case858 ∈ rowCases760 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits760 : ∀ entry ∈ rowCases760, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case667_fitted, (List.forall_mem_cons.mpr ⟨case858_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked760 : ∀ entry ∈ rowCases760, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame667_checked, (List.forall_mem_cons.mpr ⟨frame858_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero760 : ∀ entry ∈ rowCases760, entry.hero = 400 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection760 : ∀ entry ∈ rowCases760, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase760 : ∀ entry ∈ rowCases760, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases761 : List PhysicalCase := []
theorem rowFits761 : ∀ entry ∈ rowCases761, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked761 : ∀ entry ∈ rowCases761, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero761 : ∀ entry ∈ rowCases761, entry.hero = 400 := by exact (by intro entry member; cases member)
theorem rowDirection761 : ∀ entry ∈ rowCases761, entry.direction = .south := by exact (by intro entry member; cases member)
theorem rowPhase761 : ∀ entry ∈ rowCases761, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases762 : List PhysicalCase := []
theorem rowFits762 : ∀ entry ∈ rowCases762, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked762 : ∀ entry ∈ rowCases762, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero762 : ∀ entry ∈ rowCases762, entry.hero = 400 := by exact (by intro entry member; cases member)
theorem rowDirection762 : ∀ entry ∈ rowCases762, entry.direction = .east := by exact (by intro entry member; cases member)
theorem rowPhase762 : ∀ entry ∈ rowCases762, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases763 : List PhysicalCase := [case668]
theorem memberCase668 : case668 ∈ rowCases763 := by exact List.mem_cons_self
theorem rowFits763 : ∀ entry ∈ rowCases763, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case668_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked763 : ∀ entry ∈ rowCases763, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame668_checked, (by intro entry member; cases member)⟩)
theorem rowHero763 : ∀ entry ∈ rowCases763, entry.hero = 400 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection763 : ∀ entry ∈ rowCases763, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase763 : ∀ entry ∈ rowCases763, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases764 : List PhysicalCase := []
theorem rowFits764 : ∀ entry ∈ rowCases764, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked764 : ∀ entry ∈ rowCases764, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero764 : ∀ entry ∈ rowCases764, entry.hero = 400 := by exact (by intro entry member; cases member)
theorem rowDirection764 : ∀ entry ∈ rowCases764, entry.direction = .northEast := by exact (by intro entry member; cases member)
theorem rowPhase764 : ∀ entry ∈ rowCases764, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases765 : List PhysicalCase := [case669]
theorem memberCase669 : case669 ∈ rowCases765 := by exact List.mem_cons_self
theorem rowFits765 : ∀ entry ∈ rowCases765, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case669_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked765 : ∀ entry ∈ rowCases765, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame669_checked, (by intro entry member; cases member)⟩)
theorem rowHero765 : ∀ entry ∈ rowCases765, entry.hero = 400 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection765 : ∀ entry ∈ rowCases765, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase765 : ∀ entry ∈ rowCases765, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases766 : List PhysicalCase := []
theorem rowFits766 : ∀ entry ∈ rowCases766, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked766 : ∀ entry ∈ rowCases766, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero766 : ∀ entry ∈ rowCases766, entry.hero = 400 := by exact (by intro entry member; cases member)
theorem rowDirection766 : ∀ entry ∈ rowCases766, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase766 : ∀ entry ∈ rowCases766, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases767 : List PhysicalCase := []
theorem rowFits767 : ∀ entry ∈ rowCases767, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked767 : ∀ entry ∈ rowCases767, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero767 : ∀ entry ∈ rowCases767, entry.hero = 400 := by exact (by intro entry member; cases member)
theorem rowDirection767 : ∀ entry ∈ rowCases767, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase767 : ∀ entry ∈ rowCases767, entry.phase = 3 := by exact (by intro entry member; cases member)
end NetHack.Soko12Forward220.Unified.P03
