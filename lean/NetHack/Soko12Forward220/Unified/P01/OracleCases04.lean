import NetHack.Soko12Forward220.Unified.P01.OracleCases03
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P01
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
noncomputable def rowCases200 : List PhysicalCase := [case154, case684]
theorem memberCase154 : case154 ∈ rowCases200 := by exact List.mem_cons_self
theorem memberCase684 : case684 ∈ rowCases200 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits200 : ∀ entry ∈ rowCases200, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case154_fitted, (List.forall_mem_cons.mpr ⟨case684_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked200 : ∀ entry ∈ rowCases200, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame154_checked, (List.forall_mem_cons.mpr ⟨frame684_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero200 : ∀ entry ∈ rowCases200, entry.hero = 160 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection200 : ∀ entry ∈ rowCases200, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase200 : ∀ entry ∈ rowCases200, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases201 : List PhysicalCase := [case155, case729]
theorem memberCase155 : case155 ∈ rowCases201 := by exact List.mem_cons_self
theorem memberCase729 : case729 ∈ rowCases201 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits201 : ∀ entry ∈ rowCases201, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case155_fitted, (List.forall_mem_cons.mpr ⟨case729_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked201 : ∀ entry ∈ rowCases201, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame155_checked, (List.forall_mem_cons.mpr ⟨frame729_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero201 : ∀ entry ∈ rowCases201, entry.hero = 160 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection201 : ∀ entry ∈ rowCases201, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase201 : ∀ entry ∈ rowCases201, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases202 : List PhysicalCase := [case156]
theorem memberCase156 : case156 ∈ rowCases202 := by exact List.mem_cons_self
theorem rowFits202 : ∀ entry ∈ rowCases202, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case156_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked202 : ∀ entry ∈ rowCases202, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame156_checked, (by intro entry member; cases member)⟩)
theorem rowHero202 : ∀ entry ∈ rowCases202, entry.hero = 160 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection202 : ∀ entry ∈ rowCases202, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase202 : ∀ entry ∈ rowCases202, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases203 : List PhysicalCase := [case157, case705]
theorem memberCase157 : case157 ∈ rowCases203 := by exact List.mem_cons_self
theorem memberCase705 : case705 ∈ rowCases203 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits203 : ∀ entry ∈ rowCases203, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case157_fitted, (List.forall_mem_cons.mpr ⟨case705_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked203 : ∀ entry ∈ rowCases203, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame157_checked, (List.forall_mem_cons.mpr ⟨frame705_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero203 : ∀ entry ∈ rowCases203, entry.hero = 160 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection203 : ∀ entry ∈ rowCases203, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase203 : ∀ entry ∈ rowCases203, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases204 : List PhysicalCase := [case158, case159]
theorem memberCase158 : case158 ∈ rowCases204 := by exact List.mem_cons_self
theorem memberCase159 : case159 ∈ rowCases204 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits204 : ∀ entry ∈ rowCases204, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case158_fitted, (List.forall_mem_cons.mpr ⟨case159_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked204 : ∀ entry ∈ rowCases204, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame158_checked, (List.forall_mem_cons.mpr ⟨frame159_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero204 : ∀ entry ∈ rowCases204, entry.hero = 160 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection204 : ∀ entry ∈ rowCases204, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase204 : ∀ entry ∈ rowCases204, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases205 : List PhysicalCase := [case160, case161]
theorem memberCase160 : case160 ∈ rowCases205 := by exact List.mem_cons_self
theorem memberCase161 : case161 ∈ rowCases205 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits205 : ∀ entry ∈ rowCases205, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case160_fitted, (List.forall_mem_cons.mpr ⟨case161_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked205 : ∀ entry ∈ rowCases205, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame160_checked, (List.forall_mem_cons.mpr ⟨frame161_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero205 : ∀ entry ∈ rowCases205, entry.hero = 160 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection205 : ∀ entry ∈ rowCases205, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase205 : ∀ entry ∈ rowCases205, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases206 : List PhysicalCase := [case162, case163]
theorem memberCase162 : case162 ∈ rowCases206 := by exact List.mem_cons_self
theorem memberCase163 : case163 ∈ rowCases206 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits206 : ∀ entry ∈ rowCases206, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case162_fitted, (List.forall_mem_cons.mpr ⟨case163_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked206 : ∀ entry ∈ rowCases206, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame162_checked, (List.forall_mem_cons.mpr ⟨frame163_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero206 : ∀ entry ∈ rowCases206, entry.hero = 160 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection206 : ∀ entry ∈ rowCases206, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase206 : ∀ entry ∈ rowCases206, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases207 : List PhysicalCase := [case164, case165]
theorem memberCase164 : case164 ∈ rowCases207 := by exact List.mem_cons_self
theorem memberCase165 : case165 ∈ rowCases207 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits207 : ∀ entry ∈ rowCases207, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case164_fitted, (List.forall_mem_cons.mpr ⟨case165_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked207 : ∀ entry ∈ rowCases207, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame164_checked, (List.forall_mem_cons.mpr ⟨frame165_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero207 : ∀ entry ∈ rowCases207, entry.hero = 160 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection207 : ∀ entry ∈ rowCases207, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase207 : ∀ entry ∈ rowCases207, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases208 : List PhysicalCase := [case166]
theorem memberCase166 : case166 ∈ rowCases208 := by exact List.mem_cons_self
theorem rowFits208 : ∀ entry ∈ rowCases208, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case166_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked208 : ∀ entry ∈ rowCases208, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame166_checked, (by intro entry member; cases member)⟩)
theorem rowHero208 : ∀ entry ∈ rowCases208, entry.hero = 161 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection208 : ∀ entry ∈ rowCases208, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase208 : ∀ entry ∈ rowCases208, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases209 : List PhysicalCase := [case167, case733]
theorem memberCase167 : case167 ∈ rowCases209 := by exact List.mem_cons_self
theorem memberCase733 : case733 ∈ rowCases209 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits209 : ∀ entry ∈ rowCases209, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case167_fitted, (List.forall_mem_cons.mpr ⟨case733_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked209 : ∀ entry ∈ rowCases209, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame167_checked, (List.forall_mem_cons.mpr ⟨frame733_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero209 : ∀ entry ∈ rowCases209, entry.hero = 161 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection209 : ∀ entry ∈ rowCases209, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase209 : ∀ entry ∈ rowCases209, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases210 : List PhysicalCase := []
theorem rowFits210 : ∀ entry ∈ rowCases210, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked210 : ∀ entry ∈ rowCases210, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero210 : ∀ entry ∈ rowCases210, entry.hero = 161 := by exact (by intro entry member; cases member)
theorem rowDirection210 : ∀ entry ∈ rowCases210, entry.direction = .east := by exact (by intro entry member; cases member)
theorem rowPhase210 : ∀ entry ∈ rowCases210, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases211 : List PhysicalCase := [case168, case709]
theorem memberCase168 : case168 ∈ rowCases211 := by exact List.mem_cons_self
theorem memberCase709 : case709 ∈ rowCases211 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits211 : ∀ entry ∈ rowCases211, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case168_fitted, (List.forall_mem_cons.mpr ⟨case709_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked211 : ∀ entry ∈ rowCases211, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame168_checked, (List.forall_mem_cons.mpr ⟨frame709_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero211 : ∀ entry ∈ rowCases211, entry.hero = 161 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection211 : ∀ entry ∈ rowCases211, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase211 : ∀ entry ∈ rowCases211, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases212 : List PhysicalCase := []
theorem rowFits212 : ∀ entry ∈ rowCases212, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked212 : ∀ entry ∈ rowCases212, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero212 : ∀ entry ∈ rowCases212, entry.hero = 161 := by exact (by intro entry member; cases member)
theorem rowDirection212 : ∀ entry ∈ rowCases212, entry.direction = .northEast := by exact (by intro entry member; cases member)
theorem rowPhase212 : ∀ entry ∈ rowCases212, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases213 : List PhysicalCase := [case169, case170]
theorem memberCase169 : case169 ∈ rowCases213 := by exact List.mem_cons_self
theorem memberCase170 : case170 ∈ rowCases213 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits213 : ∀ entry ∈ rowCases213, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case169_fitted, (List.forall_mem_cons.mpr ⟨case170_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked213 : ∀ entry ∈ rowCases213, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame169_checked, (List.forall_mem_cons.mpr ⟨frame170_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero213 : ∀ entry ∈ rowCases213, entry.hero = 161 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection213 : ∀ entry ∈ rowCases213, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase213 : ∀ entry ∈ rowCases213, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases214 : List PhysicalCase := []
theorem rowFits214 : ∀ entry ∈ rowCases214, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked214 : ∀ entry ∈ rowCases214, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero214 : ∀ entry ∈ rowCases214, entry.hero = 161 := by exact (by intro entry member; cases member)
theorem rowDirection214 : ∀ entry ∈ rowCases214, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase214 : ∀ entry ∈ rowCases214, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases215 : List PhysicalCase := [case171, case172]
theorem memberCase171 : case171 ∈ rowCases215 := by exact List.mem_cons_self
theorem memberCase172 : case172 ∈ rowCases215 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits215 : ∀ entry ∈ rowCases215, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case171_fitted, (List.forall_mem_cons.mpr ⟨case172_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked215 : ∀ entry ∈ rowCases215, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame171_checked, (List.forall_mem_cons.mpr ⟨frame172_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero215 : ∀ entry ∈ rowCases215, entry.hero = 161 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection215 : ∀ entry ∈ rowCases215, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase215 : ∀ entry ∈ rowCases215, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases216 : List PhysicalCase := []
theorem rowFits216 : ∀ entry ∈ rowCases216, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked216 : ∀ entry ∈ rowCases216, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero216 : ∀ entry ∈ rowCases216, entry.hero = 163 := by exact (by intro entry member; cases member)
theorem rowDirection216 : ∀ entry ∈ rowCases216, entry.direction = .north := by exact (by intro entry member; cases member)
theorem rowPhase216 : ∀ entry ∈ rowCases216, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases217 : List PhysicalCase := [case173, case735]
theorem memberCase173 : case173 ∈ rowCases217 := by exact List.mem_cons_self
theorem memberCase735 : case735 ∈ rowCases217 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits217 : ∀ entry ∈ rowCases217, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case173_fitted, (List.forall_mem_cons.mpr ⟨case735_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked217 : ∀ entry ∈ rowCases217, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame173_checked, (List.forall_mem_cons.mpr ⟨frame735_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero217 : ∀ entry ∈ rowCases217, entry.hero = 163 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection217 : ∀ entry ∈ rowCases217, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase217 : ∀ entry ∈ rowCases217, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases218 : List PhysicalCase := [case174]
theorem memberCase174 : case174 ∈ rowCases218 := by exact List.mem_cons_self
theorem rowFits218 : ∀ entry ∈ rowCases218, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case174_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked218 : ∀ entry ∈ rowCases218, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame174_checked, (by intro entry member; cases member)⟩)
theorem rowHero218 : ∀ entry ∈ rowCases218, entry.hero = 163 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection218 : ∀ entry ∈ rowCases218, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase218 : ∀ entry ∈ rowCases218, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases219 : List PhysicalCase := []
theorem rowFits219 : ∀ entry ∈ rowCases219, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked219 : ∀ entry ∈ rowCases219, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero219 : ∀ entry ∈ rowCases219, entry.hero = 163 := by exact (by intro entry member; cases member)
theorem rowDirection219 : ∀ entry ∈ rowCases219, entry.direction = .west := by exact (by intro entry member; cases member)
theorem rowPhase219 : ∀ entry ∈ rowCases219, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases220 : List PhysicalCase := []
theorem rowFits220 : ∀ entry ∈ rowCases220, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked220 : ∀ entry ∈ rowCases220, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero220 : ∀ entry ∈ rowCases220, entry.hero = 163 := by exact (by intro entry member; cases member)
theorem rowDirection220 : ∀ entry ∈ rowCases220, entry.direction = .northEast := by exact (by intro entry member; cases member)
theorem rowPhase220 : ∀ entry ∈ rowCases220, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases221 : List PhysicalCase := []
theorem rowFits221 : ∀ entry ∈ rowCases221, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked221 : ∀ entry ∈ rowCases221, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero221 : ∀ entry ∈ rowCases221, entry.hero = 163 := by exact (by intro entry member; cases member)
theorem rowDirection221 : ∀ entry ∈ rowCases221, entry.direction = .northWest := by exact (by intro entry member; cases member)
theorem rowPhase221 : ∀ entry ∈ rowCases221, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases222 : List PhysicalCase := [case175, case176]
theorem memberCase175 : case175 ∈ rowCases222 := by exact List.mem_cons_self
theorem memberCase176 : case176 ∈ rowCases222 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits222 : ∀ entry ∈ rowCases222, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case175_fitted, (List.forall_mem_cons.mpr ⟨case176_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked222 : ∀ entry ∈ rowCases222, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame175_checked, (List.forall_mem_cons.mpr ⟨frame176_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero222 : ∀ entry ∈ rowCases222, entry.hero = 163 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection222 : ∀ entry ∈ rowCases222, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase222 : ∀ entry ∈ rowCases222, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases223 : List PhysicalCase := []
theorem rowFits223 : ∀ entry ∈ rowCases223, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked223 : ∀ entry ∈ rowCases223, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero223 : ∀ entry ∈ rowCases223, entry.hero = 163 := by exact (by intro entry member; cases member)
theorem rowDirection223 : ∀ entry ∈ rowCases223, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase223 : ∀ entry ∈ rowCases223, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases224 : List PhysicalCase := []
theorem rowFits224 : ∀ entry ∈ rowCases224, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked224 : ∀ entry ∈ rowCases224, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero224 : ∀ entry ∈ rowCases224, entry.hero = 164 := by exact (by intro entry member; cases member)
theorem rowDirection224 : ∀ entry ∈ rowCases224, entry.direction = .north := by exact (by intro entry member; cases member)
theorem rowPhase224 : ∀ entry ∈ rowCases224, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases225 : List PhysicalCase := [case177, case737]
theorem memberCase177 : case177 ∈ rowCases225 := by exact List.mem_cons_self
theorem memberCase737 : case737 ∈ rowCases225 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits225 : ∀ entry ∈ rowCases225, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case177_fitted, (List.forall_mem_cons.mpr ⟨case737_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked225 : ∀ entry ∈ rowCases225, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame177_checked, (List.forall_mem_cons.mpr ⟨frame737_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero225 : ∀ entry ∈ rowCases225, entry.hero = 164 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection225 : ∀ entry ∈ rowCases225, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase225 : ∀ entry ∈ rowCases225, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases226 : List PhysicalCase := []
theorem rowFits226 : ∀ entry ∈ rowCases226, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked226 : ∀ entry ∈ rowCases226, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero226 : ∀ entry ∈ rowCases226, entry.hero = 164 := by exact (by intro entry member; cases member)
theorem rowDirection226 : ∀ entry ∈ rowCases226, entry.direction = .east := by exact (by intro entry member; cases member)
theorem rowPhase226 : ∀ entry ∈ rowCases226, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases227 : List PhysicalCase := [case178]
theorem memberCase178 : case178 ∈ rowCases227 := by exact List.mem_cons_self
theorem rowFits227 : ∀ entry ∈ rowCases227, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case178_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked227 : ∀ entry ∈ rowCases227, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame178_checked, (by intro entry member; cases member)⟩)
theorem rowHero227 : ∀ entry ∈ rowCases227, entry.hero = 164 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection227 : ∀ entry ∈ rowCases227, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase227 : ∀ entry ∈ rowCases227, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases228 : List PhysicalCase := []
theorem rowFits228 : ∀ entry ∈ rowCases228, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked228 : ∀ entry ∈ rowCases228, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero228 : ∀ entry ∈ rowCases228, entry.hero = 164 := by exact (by intro entry member; cases member)
theorem rowDirection228 : ∀ entry ∈ rowCases228, entry.direction = .northEast := by exact (by intro entry member; cases member)
theorem rowPhase228 : ∀ entry ∈ rowCases228, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases229 : List PhysicalCase := []
theorem rowFits229 : ∀ entry ∈ rowCases229, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked229 : ∀ entry ∈ rowCases229, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero229 : ∀ entry ∈ rowCases229, entry.hero = 164 := by exact (by intro entry member; cases member)
theorem rowDirection229 : ∀ entry ∈ rowCases229, entry.direction = .northWest := by exact (by intro entry member; cases member)
theorem rowPhase229 : ∀ entry ∈ rowCases229, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases230 : List PhysicalCase := [case179]
theorem memberCase179 : case179 ∈ rowCases230 := by exact List.mem_cons_self
theorem rowFits230 : ∀ entry ∈ rowCases230, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case179_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked230 : ∀ entry ∈ rowCases230, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame179_checked, (by intro entry member; cases member)⟩)
theorem rowHero230 : ∀ entry ∈ rowCases230, entry.hero = 164 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection230 : ∀ entry ∈ rowCases230, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase230 : ∀ entry ∈ rowCases230, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases231 : List PhysicalCase := [case180, case181]
theorem memberCase180 : case180 ∈ rowCases231 := by exact List.mem_cons_self
theorem memberCase181 : case181 ∈ rowCases231 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits231 : ∀ entry ∈ rowCases231, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case180_fitted, (List.forall_mem_cons.mpr ⟨case181_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked231 : ∀ entry ∈ rowCases231, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame180_checked, (List.forall_mem_cons.mpr ⟨frame181_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero231 : ∀ entry ∈ rowCases231, entry.hero = 164 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection231 : ∀ entry ∈ rowCases231, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase231 : ∀ entry ∈ rowCases231, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases232 : List PhysicalCase := [case182]
theorem memberCase182 : case182 ∈ rowCases232 := by exact List.mem_cons_self
theorem rowFits232 : ∀ entry ∈ rowCases232, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case182_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked232 : ∀ entry ∈ rowCases232, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame182_checked, (by intro entry member; cases member)⟩)
theorem rowHero232 : ∀ entry ∈ rowCases232, entry.hero = 166 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection232 : ∀ entry ∈ rowCases232, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase232 : ∀ entry ∈ rowCases232, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases233 : List PhysicalCase := [case183, case743]
theorem memberCase183 : case183 ∈ rowCases233 := by exact List.mem_cons_self
theorem memberCase743 : case743 ∈ rowCases233 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits233 : ∀ entry ∈ rowCases233, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case183_fitted, (List.forall_mem_cons.mpr ⟨case743_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked233 : ∀ entry ∈ rowCases233, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame183_checked, (List.forall_mem_cons.mpr ⟨frame743_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero233 : ∀ entry ∈ rowCases233, entry.hero = 166 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection233 : ∀ entry ∈ rowCases233, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase233 : ∀ entry ∈ rowCases233, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases234 : List PhysicalCase := [case184, case716]
theorem memberCase184 : case184 ∈ rowCases234 := by exact List.mem_cons_self
theorem memberCase716 : case716 ∈ rowCases234 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits234 : ∀ entry ∈ rowCases234, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case184_fitted, (List.forall_mem_cons.mpr ⟨case716_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked234 : ∀ entry ∈ rowCases234, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame184_checked, (List.forall_mem_cons.mpr ⟨frame716_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero234 : ∀ entry ∈ rowCases234, entry.hero = 166 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection234 : ∀ entry ∈ rowCases234, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase234 : ∀ entry ∈ rowCases234, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases235 : List PhysicalCase := []
theorem rowFits235 : ∀ entry ∈ rowCases235, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked235 : ∀ entry ∈ rowCases235, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero235 : ∀ entry ∈ rowCases235, entry.hero = 166 := by exact (by intro entry member; cases member)
theorem rowDirection235 : ∀ entry ∈ rowCases235, entry.direction = .west := by exact (by intro entry member; cases member)
theorem rowPhase235 : ∀ entry ∈ rowCases235, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases236 : List PhysicalCase := [case185, case186]
theorem memberCase185 : case185 ∈ rowCases236 := by exact List.mem_cons_self
theorem memberCase186 : case186 ∈ rowCases236 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits236 : ∀ entry ∈ rowCases236, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case185_fitted, (List.forall_mem_cons.mpr ⟨case186_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked236 : ∀ entry ∈ rowCases236, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame185_checked, (List.forall_mem_cons.mpr ⟨frame186_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero236 : ∀ entry ∈ rowCases236, entry.hero = 166 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection236 : ∀ entry ∈ rowCases236, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase236 : ∀ entry ∈ rowCases236, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases237 : List PhysicalCase := []
theorem rowFits237 : ∀ entry ∈ rowCases237, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked237 : ∀ entry ∈ rowCases237, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero237 : ∀ entry ∈ rowCases237, entry.hero = 166 := by exact (by intro entry member; cases member)
theorem rowDirection237 : ∀ entry ∈ rowCases237, entry.direction = .northWest := by exact (by intro entry member; cases member)
theorem rowPhase237 : ∀ entry ∈ rowCases237, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases238 : List PhysicalCase := [case187, case188]
theorem memberCase187 : case187 ∈ rowCases238 := by exact List.mem_cons_self
theorem memberCase188 : case188 ∈ rowCases238 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits238 : ∀ entry ∈ rowCases238, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case187_fitted, (List.forall_mem_cons.mpr ⟨case188_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked238 : ∀ entry ∈ rowCases238, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame187_checked, (List.forall_mem_cons.mpr ⟨frame188_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero238 : ∀ entry ∈ rowCases238, entry.hero = 166 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection238 : ∀ entry ∈ rowCases238, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase238 : ∀ entry ∈ rowCases238, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases239 : List PhysicalCase := [case189]
theorem memberCase189 : case189 ∈ rowCases239 := by exact List.mem_cons_self
theorem rowFits239 : ∀ entry ∈ rowCases239, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case189_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked239 : ∀ entry ∈ rowCases239, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame189_checked, (by intro entry member; cases member)⟩)
theorem rowHero239 : ∀ entry ∈ rowCases239, entry.hero = 166 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection239 : ∀ entry ∈ rowCases239, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase239 : ∀ entry ∈ rowCases239, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases240 : List PhysicalCase := [case190, case688]
theorem memberCase190 : case190 ∈ rowCases240 := by exact List.mem_cons_self
theorem memberCase688 : case688 ∈ rowCases240 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits240 : ∀ entry ∈ rowCases240, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case190_fitted, (List.forall_mem_cons.mpr ⟨case688_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked240 : ∀ entry ∈ rowCases240, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame190_checked, (List.forall_mem_cons.mpr ⟨frame688_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero240 : ∀ entry ∈ rowCases240, entry.hero = 167 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection240 : ∀ entry ∈ rowCases240, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase240 : ∀ entry ∈ rowCases240, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases241 : List PhysicalCase := [case191, case747]
theorem memberCase191 : case191 ∈ rowCases241 := by exact List.mem_cons_self
theorem memberCase747 : case747 ∈ rowCases241 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits241 : ∀ entry ∈ rowCases241, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case191_fitted, (List.forall_mem_cons.mpr ⟨case747_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked241 : ∀ entry ∈ rowCases241, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame191_checked, (List.forall_mem_cons.mpr ⟨frame747_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero241 : ∀ entry ∈ rowCases241, entry.hero = 167 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection241 : ∀ entry ∈ rowCases241, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase241 : ∀ entry ∈ rowCases241, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases242 : List PhysicalCase := [case192, case720]
theorem memberCase192 : case192 ∈ rowCases242 := by exact List.mem_cons_self
theorem memberCase720 : case720 ∈ rowCases242 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits242 : ∀ entry ∈ rowCases242, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case192_fitted, (List.forall_mem_cons.mpr ⟨case720_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked242 : ∀ entry ∈ rowCases242, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame192_checked, (List.forall_mem_cons.mpr ⟨frame720_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero242 : ∀ entry ∈ rowCases242, entry.hero = 167 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection242 : ∀ entry ∈ rowCases242, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase242 : ∀ entry ∈ rowCases242, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases243 : List PhysicalCase := [case193]
theorem memberCase193 : case193 ∈ rowCases243 := by exact List.mem_cons_self
theorem rowFits243 : ∀ entry ∈ rowCases243, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case193_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked243 : ∀ entry ∈ rowCases243, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame193_checked, (by intro entry member; cases member)⟩)
theorem rowHero243 : ∀ entry ∈ rowCases243, entry.hero = 167 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection243 : ∀ entry ∈ rowCases243, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase243 : ∀ entry ∈ rowCases243, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases244 : List PhysicalCase := [case194, case195]
theorem memberCase194 : case194 ∈ rowCases244 := by exact List.mem_cons_self
theorem memberCase195 : case195 ∈ rowCases244 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits244 : ∀ entry ∈ rowCases244, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case194_fitted, (List.forall_mem_cons.mpr ⟨case195_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked244 : ∀ entry ∈ rowCases244, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame194_checked, (List.forall_mem_cons.mpr ⟨frame195_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero244 : ∀ entry ∈ rowCases244, entry.hero = 167 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection244 : ∀ entry ∈ rowCases244, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase244 : ∀ entry ∈ rowCases244, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases245 : List PhysicalCase := [case196, case197]
theorem memberCase196 : case196 ∈ rowCases245 := by exact List.mem_cons_self
theorem memberCase197 : case197 ∈ rowCases245 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits245 : ∀ entry ∈ rowCases245, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case196_fitted, (List.forall_mem_cons.mpr ⟨case197_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked245 : ∀ entry ∈ rowCases245, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame196_checked, (List.forall_mem_cons.mpr ⟨frame197_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero245 : ∀ entry ∈ rowCases245, entry.hero = 167 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection245 : ∀ entry ∈ rowCases245, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase245 : ∀ entry ∈ rowCases245, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases246 : List PhysicalCase := [case198, case199]
theorem memberCase198 : case198 ∈ rowCases246 := by exact List.mem_cons_self
theorem memberCase199 : case199 ∈ rowCases246 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits246 : ∀ entry ∈ rowCases246, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case198_fitted, (List.forall_mem_cons.mpr ⟨case199_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked246 : ∀ entry ∈ rowCases246, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame198_checked, (List.forall_mem_cons.mpr ⟨frame199_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero246 : ∀ entry ∈ rowCases246, entry.hero = 167 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection246 : ∀ entry ∈ rowCases246, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase246 : ∀ entry ∈ rowCases246, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases247 : List PhysicalCase := [case200, case201]
theorem memberCase200 : case200 ∈ rowCases247 := by exact List.mem_cons_self
theorem memberCase201 : case201 ∈ rowCases247 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits247 : ∀ entry ∈ rowCases247, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case200_fitted, (List.forall_mem_cons.mpr ⟨case201_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked247 : ∀ entry ∈ rowCases247, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame200_checked, (List.forall_mem_cons.mpr ⟨frame201_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero247 : ∀ entry ∈ rowCases247, entry.hero = 167 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection247 : ∀ entry ∈ rowCases247, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase247 : ∀ entry ∈ rowCases247, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases248 : List PhysicalCase := [case202, case692]
theorem memberCase202 : case202 ∈ rowCases248 := by exact List.mem_cons_self
theorem memberCase692 : case692 ∈ rowCases248 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits248 : ∀ entry ∈ rowCases248, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case202_fitted, (List.forall_mem_cons.mpr ⟨case692_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked248 : ∀ entry ∈ rowCases248, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame202_checked, (List.forall_mem_cons.mpr ⟨frame692_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero248 : ∀ entry ∈ rowCases248, entry.hero = 168 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection248 : ∀ entry ∈ rowCases248, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase248 : ∀ entry ∈ rowCases248, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases249 : List PhysicalCase := [case203, case751]
theorem memberCase203 : case203 ∈ rowCases249 := by exact List.mem_cons_self
theorem memberCase751 : case751 ∈ rowCases249 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits249 : ∀ entry ∈ rowCases249, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case203_fitted, (List.forall_mem_cons.mpr ⟨case751_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked249 : ∀ entry ∈ rowCases249, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame203_checked, (List.forall_mem_cons.mpr ⟨frame751_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero249 : ∀ entry ∈ rowCases249, entry.hero = 168 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection249 : ∀ entry ∈ rowCases249, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase249 : ∀ entry ∈ rowCases249, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
end NetHack.Soko12Forward220.Unified.P01
