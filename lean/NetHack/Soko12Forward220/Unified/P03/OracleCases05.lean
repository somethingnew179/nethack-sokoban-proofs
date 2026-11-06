import NetHack.Soko12Forward220.Unified.P03.OracleCases04
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P03
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
noncomputable def rowCases250 : List PhysicalCase := [case188, case720]
theorem memberCase188 : case188 ∈ rowCases250 := by exact List.mem_cons_self
theorem memberCase720 : case720 ∈ rowCases250 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits250 : ∀ entry ∈ rowCases250, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case188_fitted, (List.forall_mem_cons.mpr ⟨case720_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked250 : ∀ entry ∈ rowCases250, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame188_checked, (List.forall_mem_cons.mpr ⟨frame720_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero250 : ∀ entry ∈ rowCases250, entry.hero = 166 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection250 : ∀ entry ∈ rowCases250, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase250 : ∀ entry ∈ rowCases250, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases251 : List PhysicalCase := []
theorem rowFits251 : ∀ entry ∈ rowCases251, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked251 : ∀ entry ∈ rowCases251, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero251 : ∀ entry ∈ rowCases251, entry.hero = 166 := by exact (by intro entry member; cases member)
theorem rowDirection251 : ∀ entry ∈ rowCases251, entry.direction = .west := by exact (by intro entry member; cases member)
theorem rowPhase251 : ∀ entry ∈ rowCases251, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases252 : List PhysicalCase := [case189, case190]
theorem memberCase189 : case189 ∈ rowCases252 := by exact List.mem_cons_self
theorem memberCase190 : case190 ∈ rowCases252 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits252 : ∀ entry ∈ rowCases252, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case189_fitted, (List.forall_mem_cons.mpr ⟨case190_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked252 : ∀ entry ∈ rowCases252, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame189_checked, (List.forall_mem_cons.mpr ⟨frame190_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero252 : ∀ entry ∈ rowCases252, entry.hero = 166 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection252 : ∀ entry ∈ rowCases252, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase252 : ∀ entry ∈ rowCases252, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases253 : List PhysicalCase := []
theorem rowFits253 : ∀ entry ∈ rowCases253, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked253 : ∀ entry ∈ rowCases253, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero253 : ∀ entry ∈ rowCases253, entry.hero = 166 := by exact (by intro entry member; cases member)
theorem rowDirection253 : ∀ entry ∈ rowCases253, entry.direction = .northWest := by exact (by intro entry member; cases member)
theorem rowPhase253 : ∀ entry ∈ rowCases253, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases254 : List PhysicalCase := [case191, case192]
theorem memberCase191 : case191 ∈ rowCases254 := by exact List.mem_cons_self
theorem memberCase192 : case192 ∈ rowCases254 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits254 : ∀ entry ∈ rowCases254, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case191_fitted, (List.forall_mem_cons.mpr ⟨case192_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked254 : ∀ entry ∈ rowCases254, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame191_checked, (List.forall_mem_cons.mpr ⟨frame192_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero254 : ∀ entry ∈ rowCases254, entry.hero = 166 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection254 : ∀ entry ∈ rowCases254, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase254 : ∀ entry ∈ rowCases254, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases255 : List PhysicalCase := [case193]
theorem memberCase193 : case193 ∈ rowCases255 := by exact List.mem_cons_self
theorem rowFits255 : ∀ entry ∈ rowCases255, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case193_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked255 : ∀ entry ∈ rowCases255, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame193_checked, (by intro entry member; cases member)⟩)
theorem rowHero255 : ∀ entry ∈ rowCases255, entry.hero = 166 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection255 : ∀ entry ∈ rowCases255, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase255 : ∀ entry ∈ rowCases255, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases256 : List PhysicalCase := [case194, case692]
theorem memberCase194 : case194 ∈ rowCases256 := by exact List.mem_cons_self
theorem memberCase692 : case692 ∈ rowCases256 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits256 : ∀ entry ∈ rowCases256, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case194_fitted, (List.forall_mem_cons.mpr ⟨case692_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked256 : ∀ entry ∈ rowCases256, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame194_checked, (List.forall_mem_cons.mpr ⟨frame692_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero256 : ∀ entry ∈ rowCases256, entry.hero = 167 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection256 : ∀ entry ∈ rowCases256, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase256 : ∀ entry ∈ rowCases256, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases257 : List PhysicalCase := [case195, case751]
theorem memberCase195 : case195 ∈ rowCases257 := by exact List.mem_cons_self
theorem memberCase751 : case751 ∈ rowCases257 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits257 : ∀ entry ∈ rowCases257, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case195_fitted, (List.forall_mem_cons.mpr ⟨case751_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked257 : ∀ entry ∈ rowCases257, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame195_checked, (List.forall_mem_cons.mpr ⟨frame751_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero257 : ∀ entry ∈ rowCases257, entry.hero = 167 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection257 : ∀ entry ∈ rowCases257, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase257 : ∀ entry ∈ rowCases257, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases258 : List PhysicalCase := [case196, case724]
theorem memberCase196 : case196 ∈ rowCases258 := by exact List.mem_cons_self
theorem memberCase724 : case724 ∈ rowCases258 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits258 : ∀ entry ∈ rowCases258, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case196_fitted, (List.forall_mem_cons.mpr ⟨case724_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked258 : ∀ entry ∈ rowCases258, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame196_checked, (List.forall_mem_cons.mpr ⟨frame724_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero258 : ∀ entry ∈ rowCases258, entry.hero = 167 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection258 : ∀ entry ∈ rowCases258, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase258 : ∀ entry ∈ rowCases258, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases259 : List PhysicalCase := [case197]
theorem memberCase197 : case197 ∈ rowCases259 := by exact List.mem_cons_self
theorem rowFits259 : ∀ entry ∈ rowCases259, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case197_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked259 : ∀ entry ∈ rowCases259, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame197_checked, (by intro entry member; cases member)⟩)
theorem rowHero259 : ∀ entry ∈ rowCases259, entry.hero = 167 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection259 : ∀ entry ∈ rowCases259, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase259 : ∀ entry ∈ rowCases259, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases260 : List PhysicalCase := [case198, case199]
theorem memberCase198 : case198 ∈ rowCases260 := by exact List.mem_cons_self
theorem memberCase199 : case199 ∈ rowCases260 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits260 : ∀ entry ∈ rowCases260, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case198_fitted, (List.forall_mem_cons.mpr ⟨case199_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked260 : ∀ entry ∈ rowCases260, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame198_checked, (List.forall_mem_cons.mpr ⟨frame199_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero260 : ∀ entry ∈ rowCases260, entry.hero = 167 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection260 : ∀ entry ∈ rowCases260, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase260 : ∀ entry ∈ rowCases260, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases261 : List PhysicalCase := [case200, case201]
theorem memberCase200 : case200 ∈ rowCases261 := by exact List.mem_cons_self
theorem memberCase201 : case201 ∈ rowCases261 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits261 : ∀ entry ∈ rowCases261, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case200_fitted, (List.forall_mem_cons.mpr ⟨case201_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked261 : ∀ entry ∈ rowCases261, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame200_checked, (List.forall_mem_cons.mpr ⟨frame201_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero261 : ∀ entry ∈ rowCases261, entry.hero = 167 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection261 : ∀ entry ∈ rowCases261, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase261 : ∀ entry ∈ rowCases261, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases262 : List PhysicalCase := [case202, case203]
theorem memberCase202 : case202 ∈ rowCases262 := by exact List.mem_cons_self
theorem memberCase203 : case203 ∈ rowCases262 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits262 : ∀ entry ∈ rowCases262, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case202_fitted, (List.forall_mem_cons.mpr ⟨case203_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked262 : ∀ entry ∈ rowCases262, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame202_checked, (List.forall_mem_cons.mpr ⟨frame203_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero262 : ∀ entry ∈ rowCases262, entry.hero = 167 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection262 : ∀ entry ∈ rowCases262, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase262 : ∀ entry ∈ rowCases262, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases263 : List PhysicalCase := [case204, case205]
theorem memberCase204 : case204 ∈ rowCases263 := by exact List.mem_cons_self
theorem memberCase205 : case205 ∈ rowCases263 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits263 : ∀ entry ∈ rowCases263, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case204_fitted, (List.forall_mem_cons.mpr ⟨case205_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked263 : ∀ entry ∈ rowCases263, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame204_checked, (List.forall_mem_cons.mpr ⟨frame205_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero263 : ∀ entry ∈ rowCases263, entry.hero = 167 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection263 : ∀ entry ∈ rowCases263, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase263 : ∀ entry ∈ rowCases263, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases264 : List PhysicalCase := [case206, case696]
theorem memberCase206 : case206 ∈ rowCases264 := by exact List.mem_cons_self
theorem memberCase696 : case696 ∈ rowCases264 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits264 : ∀ entry ∈ rowCases264, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case206_fitted, (List.forall_mem_cons.mpr ⟨case696_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked264 : ∀ entry ∈ rowCases264, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame206_checked, (List.forall_mem_cons.mpr ⟨frame696_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero264 : ∀ entry ∈ rowCases264, entry.hero = 168 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection264 : ∀ entry ∈ rowCases264, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase264 : ∀ entry ∈ rowCases264, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases265 : List PhysicalCase := [case207, case755]
theorem memberCase207 : case207 ∈ rowCases265 := by exact List.mem_cons_self
theorem memberCase755 : case755 ∈ rowCases265 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits265 : ∀ entry ∈ rowCases265, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case207_fitted, (List.forall_mem_cons.mpr ⟨case755_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked265 : ∀ entry ∈ rowCases265, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame207_checked, (List.forall_mem_cons.mpr ⟨frame755_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero265 : ∀ entry ∈ rowCases265, entry.hero = 168 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection265 : ∀ entry ∈ rowCases265, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase265 : ∀ entry ∈ rowCases265, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases266 : List PhysicalCase := [case208]
theorem memberCase208 : case208 ∈ rowCases266 := by exact List.mem_cons_self
theorem rowFits266 : ∀ entry ∈ rowCases266, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case208_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked266 : ∀ entry ∈ rowCases266, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame208_checked, (by intro entry member; cases member)⟩)
theorem rowHero266 : ∀ entry ∈ rowCases266, entry.hero = 168 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection266 : ∀ entry ∈ rowCases266, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase266 : ∀ entry ∈ rowCases266, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases267 : List PhysicalCase := [case209, case721]
theorem memberCase209 : case209 ∈ rowCases267 := by exact List.mem_cons_self
theorem memberCase721 : case721 ∈ rowCases267 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits267 : ∀ entry ∈ rowCases267, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case209_fitted, (List.forall_mem_cons.mpr ⟨case721_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked267 : ∀ entry ∈ rowCases267, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame209_checked, (List.forall_mem_cons.mpr ⟨frame721_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero267 : ∀ entry ∈ rowCases267, entry.hero = 168 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection267 : ∀ entry ∈ rowCases267, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase267 : ∀ entry ∈ rowCases267, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases268 : List PhysicalCase := [case210, case211]
theorem memberCase210 : case210 ∈ rowCases268 := by exact List.mem_cons_self
theorem memberCase211 : case211 ∈ rowCases268 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits268 : ∀ entry ∈ rowCases268, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case210_fitted, (List.forall_mem_cons.mpr ⟨case211_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked268 : ∀ entry ∈ rowCases268, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame210_checked, (List.forall_mem_cons.mpr ⟨frame211_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero268 : ∀ entry ∈ rowCases268, entry.hero = 168 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection268 : ∀ entry ∈ rowCases268, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase268 : ∀ entry ∈ rowCases268, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases269 : List PhysicalCase := [case212, case213]
theorem memberCase212 : case212 ∈ rowCases269 := by exact List.mem_cons_self
theorem memberCase213 : case213 ∈ rowCases269 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits269 : ∀ entry ∈ rowCases269, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case212_fitted, (List.forall_mem_cons.mpr ⟨case213_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked269 : ∀ entry ∈ rowCases269, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame212_checked, (List.forall_mem_cons.mpr ⟨frame213_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero269 : ∀ entry ∈ rowCases269, entry.hero = 168 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection269 : ∀ entry ∈ rowCases269, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase269 : ∀ entry ∈ rowCases269, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases270 : List PhysicalCase := []
theorem rowFits270 : ∀ entry ∈ rowCases270, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked270 : ∀ entry ∈ rowCases270, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero270 : ∀ entry ∈ rowCases270, entry.hero = 168 := by exact (by intro entry member; cases member)
theorem rowDirection270 : ∀ entry ∈ rowCases270, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase270 : ∀ entry ∈ rowCases270, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases271 : List PhysicalCase := [case214, case215]
theorem memberCase214 : case214 ∈ rowCases271 := by exact List.mem_cons_self
theorem memberCase215 : case215 ∈ rowCases271 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits271 : ∀ entry ∈ rowCases271, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case214_fitted, (List.forall_mem_cons.mpr ⟨case215_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked271 : ∀ entry ∈ rowCases271, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame214_checked, (List.forall_mem_cons.mpr ⟨frame215_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero271 : ∀ entry ∈ rowCases271, entry.hero = 168 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection271 : ∀ entry ∈ rowCases271, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase271 : ∀ entry ∈ rowCases271, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases272 : List PhysicalCase := [case216, case700]
theorem memberCase216 : case216 ∈ rowCases272 := by exact List.mem_cons_self
theorem memberCase700 : case700 ∈ rowCases272 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits272 : ∀ entry ∈ rowCases272, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case216_fitted, (List.forall_mem_cons.mpr ⟨case700_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked272 : ∀ entry ∈ rowCases272, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame216_checked, (List.forall_mem_cons.mpr ⟨frame700_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero272 : ∀ entry ∈ rowCases272, entry.hero = 169 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection272 : ∀ entry ∈ rowCases272, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase272 : ∀ entry ∈ rowCases272, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases273 : List PhysicalCase := []
theorem rowFits273 : ∀ entry ∈ rowCases273, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked273 : ∀ entry ∈ rowCases273, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero273 : ∀ entry ∈ rowCases273, entry.hero = 169 := by exact (by intro entry member; cases member)
theorem rowDirection273 : ∀ entry ∈ rowCases273, entry.direction = .south := by exact (by intro entry member; cases member)
theorem rowPhase273 : ∀ entry ∈ rowCases273, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases274 : List PhysicalCase := []
theorem rowFits274 : ∀ entry ∈ rowCases274, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked274 : ∀ entry ∈ rowCases274, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero274 : ∀ entry ∈ rowCases274, entry.hero = 169 := by exact (by intro entry member; cases member)
theorem rowDirection274 : ∀ entry ∈ rowCases274, entry.direction = .east := by exact (by intro entry member; cases member)
theorem rowPhase274 : ∀ entry ∈ rowCases274, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases275 : List PhysicalCase := [case217, case725]
theorem memberCase217 : case217 ∈ rowCases275 := by exact List.mem_cons_self
theorem memberCase725 : case725 ∈ rowCases275 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits275 : ∀ entry ∈ rowCases275, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case217_fitted, (List.forall_mem_cons.mpr ⟨case725_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked275 : ∀ entry ∈ rowCases275, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame217_checked, (List.forall_mem_cons.mpr ⟨frame725_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero275 : ∀ entry ∈ rowCases275, entry.hero = 169 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection275 : ∀ entry ∈ rowCases275, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase275 : ∀ entry ∈ rowCases275, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases276 : List PhysicalCase := []
theorem rowFits276 : ∀ entry ∈ rowCases276, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked276 : ∀ entry ∈ rowCases276, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero276 : ∀ entry ∈ rowCases276, entry.hero = 169 := by exact (by intro entry member; cases member)
theorem rowDirection276 : ∀ entry ∈ rowCases276, entry.direction = .northEast := by exact (by intro entry member; cases member)
theorem rowPhase276 : ∀ entry ∈ rowCases276, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases277 : List PhysicalCase := [case218, case219]
theorem memberCase218 : case218 ∈ rowCases277 := by exact List.mem_cons_self
theorem memberCase219 : case219 ∈ rowCases277 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits277 : ∀ entry ∈ rowCases277, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case218_fitted, (List.forall_mem_cons.mpr ⟨case219_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked277 : ∀ entry ∈ rowCases277, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame218_checked, (List.forall_mem_cons.mpr ⟨frame219_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero277 : ∀ entry ∈ rowCases277, entry.hero = 169 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection277 : ∀ entry ∈ rowCases277, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase277 : ∀ entry ∈ rowCases277, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases278 : List PhysicalCase := []
theorem rowFits278 : ∀ entry ∈ rowCases278, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked278 : ∀ entry ∈ rowCases278, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero278 : ∀ entry ∈ rowCases278, entry.hero = 169 := by exact (by intro entry member; cases member)
theorem rowDirection278 : ∀ entry ∈ rowCases278, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase278 : ∀ entry ∈ rowCases278, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases279 : List PhysicalCase := [case220]
theorem memberCase220 : case220 ∈ rowCases279 := by exact List.mem_cons_self
theorem rowFits279 : ∀ entry ∈ rowCases279, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case220_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked279 : ∀ entry ∈ rowCases279, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame220_checked, (by intro entry member; cases member)⟩)
theorem rowHero279 : ∀ entry ∈ rowCases279, entry.hero = 169 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection279 : ∀ entry ∈ rowCases279, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase279 : ∀ entry ∈ rowCases279, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases280 : List PhysicalCase := [case221, case702]
theorem memberCase221 : case221 ∈ rowCases280 := by exact List.mem_cons_self
theorem memberCase702 : case702 ∈ rowCases280 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits280 : ∀ entry ∈ rowCases280, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case221_fitted, (List.forall_mem_cons.mpr ⟨case702_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked280 : ∀ entry ∈ rowCases280, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame221_checked, (List.forall_mem_cons.mpr ⟨frame702_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero280 : ∀ entry ∈ rowCases280, entry.hero = 184 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection280 : ∀ entry ∈ rowCases280, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase280 : ∀ entry ∈ rowCases280, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases281 : List PhysicalCase := [case222, case757]
theorem memberCase222 : case222 ∈ rowCases281 := by exact List.mem_cons_self
theorem memberCase757 : case757 ∈ rowCases281 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits281 : ∀ entry ∈ rowCases281, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case222_fitted, (List.forall_mem_cons.mpr ⟨case757_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked281 : ∀ entry ∈ rowCases281, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame222_checked, (List.forall_mem_cons.mpr ⟨frame757_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero281 : ∀ entry ∈ rowCases281, entry.hero = 184 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection281 : ∀ entry ∈ rowCases281, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase281 : ∀ entry ∈ rowCases281, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases282 : List PhysicalCase := [case223, case730]
theorem memberCase223 : case223 ∈ rowCases282 := by exact List.mem_cons_self
theorem memberCase730 : case730 ∈ rowCases282 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits282 : ∀ entry ∈ rowCases282, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case223_fitted, (List.forall_mem_cons.mpr ⟨case730_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked282 : ∀ entry ∈ rowCases282, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame223_checked, (List.forall_mem_cons.mpr ⟨frame730_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero282 : ∀ entry ∈ rowCases282, entry.hero = 184 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection282 : ∀ entry ∈ rowCases282, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase282 : ∀ entry ∈ rowCases282, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases283 : List PhysicalCase := []
theorem rowFits283 : ∀ entry ∈ rowCases283, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked283 : ∀ entry ∈ rowCases283, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero283 : ∀ entry ∈ rowCases283, entry.hero = 184 := by exact (by intro entry member; cases member)
theorem rowDirection283 : ∀ entry ∈ rowCases283, entry.direction = .west := by exact (by intro entry member; cases member)
theorem rowPhase283 : ∀ entry ∈ rowCases283, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases284 : List PhysicalCase := [case224, case225]
theorem memberCase224 : case224 ∈ rowCases284 := by exact List.mem_cons_self
theorem memberCase225 : case225 ∈ rowCases284 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits284 : ∀ entry ∈ rowCases284, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case224_fitted, (List.forall_mem_cons.mpr ⟨case225_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked284 : ∀ entry ∈ rowCases284, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame224_checked, (List.forall_mem_cons.mpr ⟨frame225_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero284 : ∀ entry ∈ rowCases284, entry.hero = 184 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection284 : ∀ entry ∈ rowCases284, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase284 : ∀ entry ∈ rowCases284, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases285 : List PhysicalCase := [case226]
theorem memberCase226 : case226 ∈ rowCases285 := by exact List.mem_cons_self
theorem rowFits285 : ∀ entry ∈ rowCases285, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case226_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked285 : ∀ entry ∈ rowCases285, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame226_checked, (by intro entry member; cases member)⟩)
theorem rowHero285 : ∀ entry ∈ rowCases285, entry.hero = 184 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection285 : ∀ entry ∈ rowCases285, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase285 : ∀ entry ∈ rowCases285, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases286 : List PhysicalCase := [case227, case228]
theorem memberCase227 : case227 ∈ rowCases286 := by exact List.mem_cons_self
theorem memberCase228 : case228 ∈ rowCases286 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits286 : ∀ entry ∈ rowCases286, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case227_fitted, (List.forall_mem_cons.mpr ⟨case228_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked286 : ∀ entry ∈ rowCases286, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame227_checked, (List.forall_mem_cons.mpr ⟨frame228_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero286 : ∀ entry ∈ rowCases286, entry.hero = 184 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection286 : ∀ entry ∈ rowCases286, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase286 : ∀ entry ∈ rowCases286, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases287 : List PhysicalCase := []
theorem rowFits287 : ∀ entry ∈ rowCases287, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked287 : ∀ entry ∈ rowCases287, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero287 : ∀ entry ∈ rowCases287, entry.hero = 184 := by exact (by intro entry member; cases member)
theorem rowDirection287 : ∀ entry ∈ rowCases287, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase287 : ∀ entry ∈ rowCases287, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases288 : List PhysicalCase := [case229, case706]
theorem memberCase229 : case229 ∈ rowCases288 := by exact List.mem_cons_self
theorem memberCase706 : case706 ∈ rowCases288 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits288 : ∀ entry ∈ rowCases288, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case229_fitted, (List.forall_mem_cons.mpr ⟨case706_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked288 : ∀ entry ∈ rowCases288, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame229_checked, (List.forall_mem_cons.mpr ⟨frame706_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero288 : ∀ entry ∈ rowCases288, entry.hero = 185 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection288 : ∀ entry ∈ rowCases288, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase288 : ∀ entry ∈ rowCases288, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases289 : List PhysicalCase := [case230, case759]
theorem memberCase230 : case230 ∈ rowCases289 := by exact List.mem_cons_self
theorem memberCase759 : case759 ∈ rowCases289 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits289 : ∀ entry ∈ rowCases289, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case230_fitted, (List.forall_mem_cons.mpr ⟨case759_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked289 : ∀ entry ∈ rowCases289, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame230_checked, (List.forall_mem_cons.mpr ⟨frame759_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero289 : ∀ entry ∈ rowCases289, entry.hero = 185 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection289 : ∀ entry ∈ rowCases289, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase289 : ∀ entry ∈ rowCases289, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases290 : List PhysicalCase := [case231, case734]
theorem memberCase231 : case231 ∈ rowCases290 := by exact List.mem_cons_self
theorem memberCase734 : case734 ∈ rowCases290 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits290 : ∀ entry ∈ rowCases290, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case231_fitted, (List.forall_mem_cons.mpr ⟨case734_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked290 : ∀ entry ∈ rowCases290, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame231_checked, (List.forall_mem_cons.mpr ⟨frame734_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero290 : ∀ entry ∈ rowCases290, entry.hero = 185 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection290 : ∀ entry ∈ rowCases290, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase290 : ∀ entry ∈ rowCases290, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases291 : List PhysicalCase := [case232]
theorem memberCase232 : case232 ∈ rowCases291 := by exact List.mem_cons_self
theorem rowFits291 : ∀ entry ∈ rowCases291, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case232_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked291 : ∀ entry ∈ rowCases291, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame232_checked, (by intro entry member; cases member)⟩)
theorem rowHero291 : ∀ entry ∈ rowCases291, entry.hero = 185 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection291 : ∀ entry ∈ rowCases291, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase291 : ∀ entry ∈ rowCases291, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases292 : List PhysicalCase := [case233, case234]
theorem memberCase233 : case233 ∈ rowCases292 := by exact List.mem_cons_self
theorem memberCase234 : case234 ∈ rowCases292 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits292 : ∀ entry ∈ rowCases292, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case233_fitted, (List.forall_mem_cons.mpr ⟨case234_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked292 : ∀ entry ∈ rowCases292, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame233_checked, (List.forall_mem_cons.mpr ⟨frame234_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero292 : ∀ entry ∈ rowCases292, entry.hero = 185 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection292 : ∀ entry ∈ rowCases292, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase292 : ∀ entry ∈ rowCases292, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases293 : List PhysicalCase := [case235, case236]
theorem memberCase235 : case235 ∈ rowCases293 := by exact List.mem_cons_self
theorem memberCase236 : case236 ∈ rowCases293 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits293 : ∀ entry ∈ rowCases293, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case235_fitted, (List.forall_mem_cons.mpr ⟨case236_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked293 : ∀ entry ∈ rowCases293, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame235_checked, (List.forall_mem_cons.mpr ⟨frame236_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero293 : ∀ entry ∈ rowCases293, entry.hero = 185 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection293 : ∀ entry ∈ rowCases293, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase293 : ∀ entry ∈ rowCases293, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases294 : List PhysicalCase := [case237, case238]
theorem memberCase237 : case237 ∈ rowCases294 := by exact List.mem_cons_self
theorem memberCase238 : case238 ∈ rowCases294 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits294 : ∀ entry ∈ rowCases294, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case237_fitted, (List.forall_mem_cons.mpr ⟨case238_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked294 : ∀ entry ∈ rowCases294, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame237_checked, (List.forall_mem_cons.mpr ⟨frame238_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero294 : ∀ entry ∈ rowCases294, entry.hero = 185 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection294 : ∀ entry ∈ rowCases294, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase294 : ∀ entry ∈ rowCases294, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases295 : List PhysicalCase := [case239, case240]
theorem memberCase239 : case239 ∈ rowCases295 := by exact List.mem_cons_self
theorem memberCase240 : case240 ∈ rowCases295 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits295 : ∀ entry ∈ rowCases295, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case239_fitted, (List.forall_mem_cons.mpr ⟨case240_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked295 : ∀ entry ∈ rowCases295, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame239_checked, (List.forall_mem_cons.mpr ⟨frame240_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero295 : ∀ entry ∈ rowCases295, entry.hero = 185 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection295 : ∀ entry ∈ rowCases295, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase295 : ∀ entry ∈ rowCases295, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases296 : List PhysicalCase := [case241, case710]
theorem memberCase241 : case241 ∈ rowCases296 := by exact List.mem_cons_self
theorem memberCase710 : case710 ∈ rowCases296 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits296 : ∀ entry ∈ rowCases296, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case241_fitted, (List.forall_mem_cons.mpr ⟨case710_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked296 : ∀ entry ∈ rowCases296, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame241_checked, (List.forall_mem_cons.mpr ⟨frame710_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero296 : ∀ entry ∈ rowCases296, entry.hero = 186 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection296 : ∀ entry ∈ rowCases296, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase296 : ∀ entry ∈ rowCases296, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases297 : List PhysicalCase := [case242, case763]
theorem memberCase242 : case242 ∈ rowCases297 := by exact List.mem_cons_self
theorem memberCase763 : case763 ∈ rowCases297 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits297 : ∀ entry ∈ rowCases297, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case242_fitted, (List.forall_mem_cons.mpr ⟨case763_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked297 : ∀ entry ∈ rowCases297, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame242_checked, (List.forall_mem_cons.mpr ⟨frame763_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero297 : ∀ entry ∈ rowCases297, entry.hero = 186 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection297 : ∀ entry ∈ rowCases297, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase297 : ∀ entry ∈ rowCases297, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases298 : List PhysicalCase := [case243]
theorem memberCase243 : case243 ∈ rowCases298 := by exact List.mem_cons_self
theorem rowFits298 : ∀ entry ∈ rowCases298, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case243_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked298 : ∀ entry ∈ rowCases298, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame243_checked, (by intro entry member; cases member)⟩)
theorem rowHero298 : ∀ entry ∈ rowCases298, entry.hero = 186 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection298 : ∀ entry ∈ rowCases298, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase298 : ∀ entry ∈ rowCases298, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases299 : List PhysicalCase := [case244, case731]
theorem memberCase244 : case244 ∈ rowCases299 := by exact List.mem_cons_self
theorem memberCase731 : case731 ∈ rowCases299 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits299 : ∀ entry ∈ rowCases299, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case244_fitted, (List.forall_mem_cons.mpr ⟨case731_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked299 : ∀ entry ∈ rowCases299, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame244_checked, (List.forall_mem_cons.mpr ⟨frame731_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero299 : ∀ entry ∈ rowCases299, entry.hero = 186 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection299 : ∀ entry ∈ rowCases299, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase299 : ∀ entry ∈ rowCases299, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
end NetHack.Soko12Forward220.Unified.P03
