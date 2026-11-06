import NetHack.Soko12Forward220.Unified.P04.OracleCases14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P04
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
noncomputable def rowCases750 : List PhysicalCase := []
theorem rowFits750 : ∀ entry ∈ rowCases750, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked750 : ∀ entry ∈ rowCases750, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero750 : ∀ entry ∈ rowCases750, entry.hero = 396 := by exact (by intro entry member; cases member)
theorem rowDirection750 : ∀ entry ∈ rowCases750, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase750 : ∀ entry ∈ rowCases750, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases751 : List PhysicalCase := []
theorem rowFits751 : ∀ entry ∈ rowCases751, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked751 : ∀ entry ∈ rowCases751, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero751 : ∀ entry ∈ rowCases751, entry.hero = 396 := by exact (by intro entry member; cases member)
theorem rowDirection751 : ∀ entry ∈ rowCases751, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase751 : ∀ entry ∈ rowCases751, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases752 : List PhysicalCase := [case660, case852]
theorem memberCase660 : case660 ∈ rowCases752 := by exact List.mem_cons_self
theorem memberCase852 : case852 ∈ rowCases752 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits752 : ∀ entry ∈ rowCases752, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case660_fitted, (List.forall_mem_cons.mpr ⟨case852_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked752 : ∀ entry ∈ rowCases752, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame660_checked, (List.forall_mem_cons.mpr ⟨frame852_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero752 : ∀ entry ∈ rowCases752, entry.hero = 397 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection752 : ∀ entry ∈ rowCases752, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase752 : ∀ entry ∈ rowCases752, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases753 : List PhysicalCase := []
theorem rowFits753 : ∀ entry ∈ rowCases753, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked753 : ∀ entry ∈ rowCases753, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero753 : ∀ entry ∈ rowCases753, entry.hero = 397 := by exact (by intro entry member; cases member)
theorem rowDirection753 : ∀ entry ∈ rowCases753, entry.direction = .south := by exact (by intro entry member; cases member)
theorem rowPhase753 : ∀ entry ∈ rowCases753, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases754 : List PhysicalCase := []
theorem rowFits754 : ∀ entry ∈ rowCases754, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked754 : ∀ entry ∈ rowCases754, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero754 : ∀ entry ∈ rowCases754, entry.hero = 397 := by exact (by intro entry member; cases member)
theorem rowDirection754 : ∀ entry ∈ rowCases754, entry.direction = .east := by exact (by intro entry member; cases member)
theorem rowPhase754 : ∀ entry ∈ rowCases754, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases755 : List PhysicalCase := [case661]
theorem memberCase661 : case661 ∈ rowCases755 := by exact List.mem_cons_self
theorem rowFits755 : ∀ entry ∈ rowCases755, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case661_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked755 : ∀ entry ∈ rowCases755, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame661_checked, (by intro entry member; cases member)⟩)
theorem rowHero755 : ∀ entry ∈ rowCases755, entry.hero = 397 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection755 : ∀ entry ∈ rowCases755, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase755 : ∀ entry ∈ rowCases755, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases756 : List PhysicalCase := [case662]
theorem memberCase662 : case662 ∈ rowCases756 := by exact List.mem_cons_self
theorem rowFits756 : ∀ entry ∈ rowCases756, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case662_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked756 : ∀ entry ∈ rowCases756, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame662_checked, (by intro entry member; cases member)⟩)
theorem rowHero756 : ∀ entry ∈ rowCases756, entry.hero = 397 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection756 : ∀ entry ∈ rowCases756, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase756 : ∀ entry ∈ rowCases756, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases757 : List PhysicalCase := [case663]
theorem memberCase663 : case663 ∈ rowCases757 := by exact List.mem_cons_self
theorem rowFits757 : ∀ entry ∈ rowCases757, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case663_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked757 : ∀ entry ∈ rowCases757, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame663_checked, (by intro entry member; cases member)⟩)
theorem rowHero757 : ∀ entry ∈ rowCases757, entry.hero = 397 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection757 : ∀ entry ∈ rowCases757, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase757 : ∀ entry ∈ rowCases757, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases758 : List PhysicalCase := []
theorem rowFits758 : ∀ entry ∈ rowCases758, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked758 : ∀ entry ∈ rowCases758, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero758 : ∀ entry ∈ rowCases758, entry.hero = 397 := by exact (by intro entry member; cases member)
theorem rowDirection758 : ∀ entry ∈ rowCases758, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase758 : ∀ entry ∈ rowCases758, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases759 : List PhysicalCase := []
theorem rowFits759 : ∀ entry ∈ rowCases759, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked759 : ∀ entry ∈ rowCases759, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero759 : ∀ entry ∈ rowCases759, entry.hero = 397 := by exact (by intro entry member; cases member)
theorem rowDirection759 : ∀ entry ∈ rowCases759, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase759 : ∀ entry ∈ rowCases759, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases760 : List PhysicalCase := [case664]
theorem memberCase664 : case664 ∈ rowCases760 := by exact List.mem_cons_self
theorem rowFits760 : ∀ entry ∈ rowCases760, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case664_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked760 : ∀ entry ∈ rowCases760, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame664_checked, (by intro entry member; cases member)⟩)
theorem rowHero760 : ∀ entry ∈ rowCases760, entry.hero = 399 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection760 : ∀ entry ∈ rowCases760, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase760 : ∀ entry ∈ rowCases760, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases761 : List PhysicalCase := []
theorem rowFits761 : ∀ entry ∈ rowCases761, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked761 : ∀ entry ∈ rowCases761, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero761 : ∀ entry ∈ rowCases761, entry.hero = 399 := by exact (by intro entry member; cases member)
theorem rowDirection761 : ∀ entry ∈ rowCases761, entry.direction = .south := by exact (by intro entry member; cases member)
theorem rowPhase761 : ∀ entry ∈ rowCases761, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases762 : List PhysicalCase := [case665]
theorem memberCase665 : case665 ∈ rowCases762 := by exact List.mem_cons_self
theorem rowFits762 : ∀ entry ∈ rowCases762, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case665_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked762 : ∀ entry ∈ rowCases762, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame665_checked, (by intro entry member; cases member)⟩)
theorem rowHero762 : ∀ entry ∈ rowCases762, entry.hero = 399 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection762 : ∀ entry ∈ rowCases762, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase762 : ∀ entry ∈ rowCases762, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases763 : List PhysicalCase := []
theorem rowFits763 : ∀ entry ∈ rowCases763, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked763 : ∀ entry ∈ rowCases763, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero763 : ∀ entry ∈ rowCases763, entry.hero = 399 := by exact (by intro entry member; cases member)
theorem rowDirection763 : ∀ entry ∈ rowCases763, entry.direction = .west := by exact (by intro entry member; cases member)
theorem rowPhase763 : ∀ entry ∈ rowCases763, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases764 : List PhysicalCase := [case666, case667]
theorem memberCase666 : case666 ∈ rowCases764 := by exact List.mem_cons_self
theorem memberCase667 : case667 ∈ rowCases764 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits764 : ∀ entry ∈ rowCases764, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case666_fitted, (List.forall_mem_cons.mpr ⟨case667_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked764 : ∀ entry ∈ rowCases764, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame666_checked, (List.forall_mem_cons.mpr ⟨frame667_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero764 : ∀ entry ∈ rowCases764, entry.hero = 399 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection764 : ∀ entry ∈ rowCases764, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase764 : ∀ entry ∈ rowCases764, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases765 : List PhysicalCase := [case668]
theorem memberCase668 : case668 ∈ rowCases765 := by exact List.mem_cons_self
theorem rowFits765 : ∀ entry ∈ rowCases765, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case668_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked765 : ∀ entry ∈ rowCases765, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame668_checked, (by intro entry member; cases member)⟩)
theorem rowHero765 : ∀ entry ∈ rowCases765, entry.hero = 399 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection765 : ∀ entry ∈ rowCases765, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase765 : ∀ entry ∈ rowCases765, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases766 : List PhysicalCase := []
theorem rowFits766 : ∀ entry ∈ rowCases766, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked766 : ∀ entry ∈ rowCases766, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero766 : ∀ entry ∈ rowCases766, entry.hero = 399 := by exact (by intro entry member; cases member)
theorem rowDirection766 : ∀ entry ∈ rowCases766, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase766 : ∀ entry ∈ rowCases766, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases767 : List PhysicalCase := []
theorem rowFits767 : ∀ entry ∈ rowCases767, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked767 : ∀ entry ∈ rowCases767, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero767 : ∀ entry ∈ rowCases767, entry.hero = 399 := by exact (by intro entry member; cases member)
theorem rowDirection767 : ∀ entry ∈ rowCases767, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase767 : ∀ entry ∈ rowCases767, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases768 : List PhysicalCase := [case669, case860]
theorem memberCase669 : case669 ∈ rowCases768 := by exact List.mem_cons_self
theorem memberCase860 : case860 ∈ rowCases768 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits768 : ∀ entry ∈ rowCases768, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case669_fitted, (List.forall_mem_cons.mpr ⟨case860_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked768 : ∀ entry ∈ rowCases768, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame669_checked, (List.forall_mem_cons.mpr ⟨frame860_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero768 : ∀ entry ∈ rowCases768, entry.hero = 400 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection768 : ∀ entry ∈ rowCases768, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase768 : ∀ entry ∈ rowCases768, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases769 : List PhysicalCase := []
theorem rowFits769 : ∀ entry ∈ rowCases769, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked769 : ∀ entry ∈ rowCases769, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero769 : ∀ entry ∈ rowCases769, entry.hero = 400 := by exact (by intro entry member; cases member)
theorem rowDirection769 : ∀ entry ∈ rowCases769, entry.direction = .south := by exact (by intro entry member; cases member)
theorem rowPhase769 : ∀ entry ∈ rowCases769, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases770 : List PhysicalCase := []
theorem rowFits770 : ∀ entry ∈ rowCases770, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked770 : ∀ entry ∈ rowCases770, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero770 : ∀ entry ∈ rowCases770, entry.hero = 400 := by exact (by intro entry member; cases member)
theorem rowDirection770 : ∀ entry ∈ rowCases770, entry.direction = .east := by exact (by intro entry member; cases member)
theorem rowPhase770 : ∀ entry ∈ rowCases770, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases771 : List PhysicalCase := [case670]
theorem memberCase670 : case670 ∈ rowCases771 := by exact List.mem_cons_self
theorem rowFits771 : ∀ entry ∈ rowCases771, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case670_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked771 : ∀ entry ∈ rowCases771, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame670_checked, (by intro entry member; cases member)⟩)
theorem rowHero771 : ∀ entry ∈ rowCases771, entry.hero = 400 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection771 : ∀ entry ∈ rowCases771, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase771 : ∀ entry ∈ rowCases771, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases772 : List PhysicalCase := []
theorem rowFits772 : ∀ entry ∈ rowCases772, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked772 : ∀ entry ∈ rowCases772, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero772 : ∀ entry ∈ rowCases772, entry.hero = 400 := by exact (by intro entry member; cases member)
theorem rowDirection772 : ∀ entry ∈ rowCases772, entry.direction = .northEast := by exact (by intro entry member; cases member)
theorem rowPhase772 : ∀ entry ∈ rowCases772, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases773 : List PhysicalCase := [case671]
theorem memberCase671 : case671 ∈ rowCases773 := by exact List.mem_cons_self
theorem rowFits773 : ∀ entry ∈ rowCases773, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case671_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked773 : ∀ entry ∈ rowCases773, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame671_checked, (by intro entry member; cases member)⟩)
theorem rowHero773 : ∀ entry ∈ rowCases773, entry.hero = 400 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection773 : ∀ entry ∈ rowCases773, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase773 : ∀ entry ∈ rowCases773, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases774 : List PhysicalCase := []
theorem rowFits774 : ∀ entry ∈ rowCases774, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked774 : ∀ entry ∈ rowCases774, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero774 : ∀ entry ∈ rowCases774, entry.hero = 400 := by exact (by intro entry member; cases member)
theorem rowDirection774 : ∀ entry ∈ rowCases774, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase774 : ∀ entry ∈ rowCases774, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases775 : List PhysicalCase := []
theorem rowFits775 : ∀ entry ∈ rowCases775, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked775 : ∀ entry ∈ rowCases775, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero775 : ∀ entry ∈ rowCases775, entry.hero = 400 := by exact (by intro entry member; cases member)
theorem rowDirection775 : ∀ entry ∈ rowCases775, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase775 : ∀ entry ∈ rowCases775, entry.phase = 4 := by exact (by intro entry member; cases member)
end NetHack.Soko12Forward220.Unified.P04
