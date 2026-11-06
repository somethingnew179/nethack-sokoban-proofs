import NetHack.Soko12Forward220.Unified.P03.OracleCases02
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P03
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
noncomputable def rowCases150 : List PhysicalCase := [case088, case089]
theorem memberCase088 : case088 ∈ rowCases150 := by exact List.mem_cons_self
theorem memberCase089 : case089 ∈ rowCases150 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits150 : ∀ entry ∈ rowCases150, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case088_fitted, (List.forall_mem_cons.mpr ⟨case089_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked150 : ∀ entry ∈ rowCases150, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame088_checked, (List.forall_mem_cons.mpr ⟨frame089_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero150 : ∀ entry ∈ rowCases150, entry.hero = 134 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection150 : ∀ entry ∈ rowCases150, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase150 : ∀ entry ∈ rowCases150, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases151 : List PhysicalCase := [case090, case091]
theorem memberCase090 : case090 ∈ rowCases151 := by exact List.mem_cons_self
theorem memberCase091 : case091 ∈ rowCases151 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits151 : ∀ entry ∈ rowCases151, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case090_fitted, (List.forall_mem_cons.mpr ⟨case091_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked151 : ∀ entry ∈ rowCases151, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame090_checked, (List.forall_mem_cons.mpr ⟨frame091_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero151 : ∀ entry ∈ rowCases151, entry.hero = 134 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection151 : ∀ entry ∈ rowCases151, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase151 : ∀ entry ∈ rowCases151, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases152 : List PhysicalCase := []
theorem rowFits152 : ∀ entry ∈ rowCases152, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked152 : ∀ entry ∈ rowCases152, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero152 : ∀ entry ∈ rowCases152, entry.hero = 135 := by exact (by intro entry member; cases member)
theorem rowDirection152 : ∀ entry ∈ rowCases152, entry.direction = .north := by exact (by intro entry member; cases member)
theorem rowPhase152 : ∀ entry ∈ rowCases152, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases153 : List PhysicalCase := [case092, case715]
theorem memberCase092 : case092 ∈ rowCases153 := by exact List.mem_cons_self
theorem memberCase715 : case715 ∈ rowCases153 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits153 : ∀ entry ∈ rowCases153, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case092_fitted, (List.forall_mem_cons.mpr ⟨case715_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked153 : ∀ entry ∈ rowCases153, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame092_checked, (List.forall_mem_cons.mpr ⟨frame715_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero153 : ∀ entry ∈ rowCases153, entry.hero = 135 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection153 : ∀ entry ∈ rowCases153, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase153 : ∀ entry ∈ rowCases153, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases154 : List PhysicalCase := []
theorem rowFits154 : ∀ entry ∈ rowCases154, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked154 : ∀ entry ∈ rowCases154, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero154 : ∀ entry ∈ rowCases154, entry.hero = 135 := by exact (by intro entry member; cases member)
theorem rowDirection154 : ∀ entry ∈ rowCases154, entry.direction = .east := by exact (by intro entry member; cases member)
theorem rowPhase154 : ∀ entry ∈ rowCases154, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases155 : List PhysicalCase := [case093, case691]
theorem memberCase093 : case093 ∈ rowCases155 := by exact List.mem_cons_self
theorem memberCase691 : case691 ∈ rowCases155 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits155 : ∀ entry ∈ rowCases155, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case093_fitted, (List.forall_mem_cons.mpr ⟨case691_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked155 : ∀ entry ∈ rowCases155, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame093_checked, (List.forall_mem_cons.mpr ⟨frame691_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero155 : ∀ entry ∈ rowCases155, entry.hero = 135 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection155 : ∀ entry ∈ rowCases155, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase155 : ∀ entry ∈ rowCases155, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases156 : List PhysicalCase := []
theorem rowFits156 : ∀ entry ∈ rowCases156, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked156 : ∀ entry ∈ rowCases156, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero156 : ∀ entry ∈ rowCases156, entry.hero = 135 := by exact (by intro entry member; cases member)
theorem rowDirection156 : ∀ entry ∈ rowCases156, entry.direction = .northEast := by exact (by intro entry member; cases member)
theorem rowPhase156 : ∀ entry ∈ rowCases156, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases157 : List PhysicalCase := [case094]
theorem memberCase094 : case094 ∈ rowCases157 := by exact List.mem_cons_self
theorem rowFits157 : ∀ entry ∈ rowCases157, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case094_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked157 : ∀ entry ∈ rowCases157, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame094_checked, (by intro entry member; cases member)⟩)
theorem rowHero157 : ∀ entry ∈ rowCases157, entry.hero = 135 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection157 : ∀ entry ∈ rowCases157, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase157 : ∀ entry ∈ rowCases157, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases158 : List PhysicalCase := []
theorem rowFits158 : ∀ entry ∈ rowCases158, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked158 : ∀ entry ∈ rowCases158, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero158 : ∀ entry ∈ rowCases158, entry.hero = 135 := by exact (by intro entry member; cases member)
theorem rowDirection158 : ∀ entry ∈ rowCases158, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase158 : ∀ entry ∈ rowCases158, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases159 : List PhysicalCase := [case095, case096]
theorem memberCase095 : case095 ∈ rowCases159 := by exact List.mem_cons_self
theorem memberCase096 : case096 ∈ rowCases159 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits159 : ∀ entry ∈ rowCases159, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case095_fitted, (List.forall_mem_cons.mpr ⟨case096_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked159 : ∀ entry ∈ rowCases159, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame095_checked, (List.forall_mem_cons.mpr ⟨frame096_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero159 : ∀ entry ∈ rowCases159, entry.hero = 135 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection159 : ∀ entry ∈ rowCases159, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase159 : ∀ entry ∈ rowCases159, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases160 : List PhysicalCase := []
theorem rowFits160 : ∀ entry ∈ rowCases160, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked160 : ∀ entry ∈ rowCases160, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero160 : ∀ entry ∈ rowCases160, entry.hero = 140 := by exact (by intro entry member; cases member)
theorem rowDirection160 : ∀ entry ∈ rowCases160, entry.direction = .north := by exact (by intro entry member; cases member)
theorem rowPhase160 : ∀ entry ∈ rowCases160, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases161 : List PhysicalCase := [case097, case717]
theorem memberCase097 : case097 ∈ rowCases161 := by exact List.mem_cons_self
theorem memberCase717 : case717 ∈ rowCases161 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits161 : ∀ entry ∈ rowCases161, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case097_fitted, (List.forall_mem_cons.mpr ⟨case717_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked161 : ∀ entry ∈ rowCases161, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame097_checked, (List.forall_mem_cons.mpr ⟨frame717_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero161 : ∀ entry ∈ rowCases161, entry.hero = 140 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection161 : ∀ entry ∈ rowCases161, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase161 : ∀ entry ∈ rowCases161, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases162 : List PhysicalCase := [case098, case694]
theorem memberCase098 : case098 ∈ rowCases162 := by exact List.mem_cons_self
theorem memberCase694 : case694 ∈ rowCases162 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits162 : ∀ entry ∈ rowCases162, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case098_fitted, (List.forall_mem_cons.mpr ⟨case694_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked162 : ∀ entry ∈ rowCases162, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame098_checked, (List.forall_mem_cons.mpr ⟨frame694_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero162 : ∀ entry ∈ rowCases162, entry.hero = 140 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection162 : ∀ entry ∈ rowCases162, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase162 : ∀ entry ∈ rowCases162, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases163 : List PhysicalCase := []
theorem rowFits163 : ∀ entry ∈ rowCases163, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked163 : ∀ entry ∈ rowCases163, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero163 : ∀ entry ∈ rowCases163, entry.hero = 140 := by exact (by intro entry member; cases member)
theorem rowDirection163 : ∀ entry ∈ rowCases163, entry.direction = .west := by exact (by intro entry member; cases member)
theorem rowPhase163 : ∀ entry ∈ rowCases163, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases164 : List PhysicalCase := [case099]
theorem memberCase099 : case099 ∈ rowCases164 := by exact List.mem_cons_self
theorem rowFits164 : ∀ entry ∈ rowCases164, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case099_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked164 : ∀ entry ∈ rowCases164, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame099_checked, (by intro entry member; cases member)⟩)
theorem rowHero164 : ∀ entry ∈ rowCases164, entry.hero = 140 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection164 : ∀ entry ∈ rowCases164, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase164 : ∀ entry ∈ rowCases164, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases165 : List PhysicalCase := []
theorem rowFits165 : ∀ entry ∈ rowCases165, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked165 : ∀ entry ∈ rowCases165, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero165 : ∀ entry ∈ rowCases165, entry.hero = 140 := by exact (by intro entry member; cases member)
theorem rowDirection165 : ∀ entry ∈ rowCases165, entry.direction = .northWest := by exact (by intro entry member; cases member)
theorem rowPhase165 : ∀ entry ∈ rowCases165, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases166 : List PhysicalCase := [case100, case101]
theorem memberCase100 : case100 ∈ rowCases166 := by exact List.mem_cons_self
theorem memberCase101 : case101 ∈ rowCases166 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits166 : ∀ entry ∈ rowCases166, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case100_fitted, (List.forall_mem_cons.mpr ⟨case101_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked166 : ∀ entry ∈ rowCases166, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame100_checked, (List.forall_mem_cons.mpr ⟨frame101_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero166 : ∀ entry ∈ rowCases166, entry.hero = 140 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection166 : ∀ entry ∈ rowCases166, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase166 : ∀ entry ∈ rowCases166, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases167 : List PhysicalCase := []
theorem rowFits167 : ∀ entry ∈ rowCases167, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked167 : ∀ entry ∈ rowCases167, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero167 : ∀ entry ∈ rowCases167, entry.hero = 140 := by exact (by intro entry member; cases member)
theorem rowDirection167 : ∀ entry ∈ rowCases167, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase167 : ∀ entry ∈ rowCases167, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases168 : List PhysicalCase := [case102]
theorem memberCase102 : case102 ∈ rowCases168 := by exact List.mem_cons_self
theorem rowFits168 : ∀ entry ∈ rowCases168, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case102_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked168 : ∀ entry ∈ rowCases168, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame102_checked, (by intro entry member; cases member)⟩)
theorem rowHero168 : ∀ entry ∈ rowCases168, entry.hero = 141 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection168 : ∀ entry ∈ rowCases168, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase168 : ∀ entry ∈ rowCases168, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases169 : List PhysicalCase := [case103, case719]
theorem memberCase103 : case103 ∈ rowCases169 := by exact List.mem_cons_self
theorem memberCase719 : case719 ∈ rowCases169 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits169 : ∀ entry ∈ rowCases169, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case103_fitted, (List.forall_mem_cons.mpr ⟨case719_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked169 : ∀ entry ∈ rowCases169, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame103_checked, (List.forall_mem_cons.mpr ⟨frame719_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero169 : ∀ entry ∈ rowCases169, entry.hero = 141 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection169 : ∀ entry ∈ rowCases169, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase169 : ∀ entry ∈ rowCases169, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases170 : List PhysicalCase := [case104, case698]
theorem memberCase104 : case104 ∈ rowCases170 := by exact List.mem_cons_self
theorem memberCase698 : case698 ∈ rowCases170 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits170 : ∀ entry ∈ rowCases170, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case104_fitted, (List.forall_mem_cons.mpr ⟨case698_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked170 : ∀ entry ∈ rowCases170, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame104_checked, (List.forall_mem_cons.mpr ⟨frame698_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero170 : ∀ entry ∈ rowCases170, entry.hero = 141 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection170 : ∀ entry ∈ rowCases170, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase170 : ∀ entry ∈ rowCases170, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases171 : List PhysicalCase := [case105]
theorem memberCase105 : case105 ∈ rowCases171 := by exact List.mem_cons_self
theorem rowFits171 : ∀ entry ∈ rowCases171, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case105_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked171 : ∀ entry ∈ rowCases171, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame105_checked, (by intro entry member; cases member)⟩)
theorem rowHero171 : ∀ entry ∈ rowCases171, entry.hero = 141 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection171 : ∀ entry ∈ rowCases171, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase171 : ∀ entry ∈ rowCases171, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases172 : List PhysicalCase := [case106, case107]
theorem memberCase106 : case106 ∈ rowCases172 := by exact List.mem_cons_self
theorem memberCase107 : case107 ∈ rowCases172 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits172 : ∀ entry ∈ rowCases172, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case106_fitted, (List.forall_mem_cons.mpr ⟨case107_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked172 : ∀ entry ∈ rowCases172, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame106_checked, (List.forall_mem_cons.mpr ⟨frame107_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero172 : ∀ entry ∈ rowCases172, entry.hero = 141 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection172 : ∀ entry ∈ rowCases172, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase172 : ∀ entry ∈ rowCases172, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases173 : List PhysicalCase := []
theorem rowFits173 : ∀ entry ∈ rowCases173, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked173 : ∀ entry ∈ rowCases173, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero173 : ∀ entry ∈ rowCases173, entry.hero = 141 := by exact (by intro entry member; cases member)
theorem rowDirection173 : ∀ entry ∈ rowCases173, entry.direction = .northWest := by exact (by intro entry member; cases member)
theorem rowPhase173 : ∀ entry ∈ rowCases173, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases174 : List PhysicalCase := [case108, case109]
theorem memberCase108 : case108 ∈ rowCases174 := by exact List.mem_cons_self
theorem memberCase109 : case109 ∈ rowCases174 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits174 : ∀ entry ∈ rowCases174, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case108_fitted, (List.forall_mem_cons.mpr ⟨case109_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked174 : ∀ entry ∈ rowCases174, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame108_checked, (List.forall_mem_cons.mpr ⟨frame109_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero174 : ∀ entry ∈ rowCases174, entry.hero = 141 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection174 : ∀ entry ∈ rowCases174, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase174 : ∀ entry ∈ rowCases174, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases175 : List PhysicalCase := [case110, case111]
theorem memberCase110 : case110 ∈ rowCases175 := by exact List.mem_cons_self
theorem memberCase111 : case111 ∈ rowCases175 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits175 : ∀ entry ∈ rowCases175, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case110_fitted, (List.forall_mem_cons.mpr ⟨case111_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked175 : ∀ entry ∈ rowCases175, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame110_checked, (List.forall_mem_cons.mpr ⟨frame111_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero175 : ∀ entry ∈ rowCases175, entry.hero = 141 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection175 : ∀ entry ∈ rowCases175, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase175 : ∀ entry ∈ rowCases175, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases176 : List PhysicalCase := [case112]
theorem memberCase112 : case112 ∈ rowCases176 := by exact List.mem_cons_self
theorem rowFits176 : ∀ entry ∈ rowCases176, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case112_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked176 : ∀ entry ∈ rowCases176, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame112_checked, (by intro entry member; cases member)⟩)
theorem rowHero176 : ∀ entry ∈ rowCases176, entry.hero = 142 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection176 : ∀ entry ∈ rowCases176, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase176 : ∀ entry ∈ rowCases176, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases177 : List PhysicalCase := [case113, case723]
theorem memberCase113 : case113 ∈ rowCases177 := by exact List.mem_cons_self
theorem memberCase723 : case723 ∈ rowCases177 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits177 : ∀ entry ∈ rowCases177, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case113_fitted, (List.forall_mem_cons.mpr ⟨case723_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked177 : ∀ entry ∈ rowCases177, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame113_checked, (List.forall_mem_cons.mpr ⟨frame723_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero177 : ∀ entry ∈ rowCases177, entry.hero = 142 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection177 : ∀ entry ∈ rowCases177, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase177 : ∀ entry ∈ rowCases177, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases178 : List PhysicalCase := [case114]
theorem memberCase114 : case114 ∈ rowCases178 := by exact List.mem_cons_self
theorem rowFits178 : ∀ entry ∈ rowCases178, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case114_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked178 : ∀ entry ∈ rowCases178, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame114_checked, (by intro entry member; cases member)⟩)
theorem rowHero178 : ∀ entry ∈ rowCases178, entry.hero = 142 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection178 : ∀ entry ∈ rowCases178, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase178 : ∀ entry ∈ rowCases178, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases179 : List PhysicalCase := [case115, case695]
theorem memberCase115 : case115 ∈ rowCases179 := by exact List.mem_cons_self
theorem memberCase695 : case695 ∈ rowCases179 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits179 : ∀ entry ∈ rowCases179, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case115_fitted, (List.forall_mem_cons.mpr ⟨case695_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked179 : ∀ entry ∈ rowCases179, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame115_checked, (List.forall_mem_cons.mpr ⟨frame695_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero179 : ∀ entry ∈ rowCases179, entry.hero = 142 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection179 : ∀ entry ∈ rowCases179, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase179 : ∀ entry ∈ rowCases179, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases180 : List PhysicalCase := [case116, case117]
theorem memberCase116 : case116 ∈ rowCases180 := by exact List.mem_cons_self
theorem memberCase117 : case117 ∈ rowCases180 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits180 : ∀ entry ∈ rowCases180, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case116_fitted, (List.forall_mem_cons.mpr ⟨case117_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked180 : ∀ entry ∈ rowCases180, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame116_checked, (List.forall_mem_cons.mpr ⟨frame117_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero180 : ∀ entry ∈ rowCases180, entry.hero = 142 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection180 : ∀ entry ∈ rowCases180, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase180 : ∀ entry ∈ rowCases180, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases181 : List PhysicalCase := [case118, case119]
theorem memberCase118 : case118 ∈ rowCases181 := by exact List.mem_cons_self
theorem memberCase119 : case119 ∈ rowCases181 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits181 : ∀ entry ∈ rowCases181, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case118_fitted, (List.forall_mem_cons.mpr ⟨case119_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked181 : ∀ entry ∈ rowCases181, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame118_checked, (List.forall_mem_cons.mpr ⟨frame119_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero181 : ∀ entry ∈ rowCases181, entry.hero = 142 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection181 : ∀ entry ∈ rowCases181, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase181 : ∀ entry ∈ rowCases181, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases182 : List PhysicalCase := [case120, case121]
theorem memberCase120 : case120 ∈ rowCases182 := by exact List.mem_cons_self
theorem memberCase121 : case121 ∈ rowCases182 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits182 : ∀ entry ∈ rowCases182, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case120_fitted, (List.forall_mem_cons.mpr ⟨case121_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked182 : ∀ entry ∈ rowCases182, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame120_checked, (List.forall_mem_cons.mpr ⟨frame121_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero182 : ∀ entry ∈ rowCases182, entry.hero = 142 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection182 : ∀ entry ∈ rowCases182, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase182 : ∀ entry ∈ rowCases182, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases183 : List PhysicalCase := [case122, case123]
theorem memberCase122 : case122 ∈ rowCases183 := by exact List.mem_cons_self
theorem memberCase123 : case123 ∈ rowCases183 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits183 : ∀ entry ∈ rowCases183, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case122_fitted, (List.forall_mem_cons.mpr ⟨case123_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked183 : ∀ entry ∈ rowCases183, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame122_checked, (List.forall_mem_cons.mpr ⟨frame123_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero183 : ∀ entry ∈ rowCases183, entry.hero = 142 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection183 : ∀ entry ∈ rowCases183, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase183 : ∀ entry ∈ rowCases183, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases184 : List PhysicalCase := [case124]
theorem memberCase124 : case124 ∈ rowCases184 := by exact List.mem_cons_self
theorem rowFits184 : ∀ entry ∈ rowCases184, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case124_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked184 : ∀ entry ∈ rowCases184, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame124_checked, (by intro entry member; cases member)⟩)
theorem rowHero184 : ∀ entry ∈ rowCases184, entry.hero = 143 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection184 : ∀ entry ∈ rowCases184, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase184 : ∀ entry ∈ rowCases184, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases185 : List PhysicalCase := [case125]
theorem memberCase125 : case125 ∈ rowCases185 := by exact List.mem_cons_self
theorem rowFits185 : ∀ entry ∈ rowCases185, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case125_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked185 : ∀ entry ∈ rowCases185, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame125_checked, (by intro entry member; cases member)⟩)
theorem rowHero185 : ∀ entry ∈ rowCases185, entry.hero = 143 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection185 : ∀ entry ∈ rowCases185, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase185 : ∀ entry ∈ rowCases185, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases186 : List PhysicalCase := []
theorem rowFits186 : ∀ entry ∈ rowCases186, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked186 : ∀ entry ∈ rowCases186, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero186 : ∀ entry ∈ rowCases186, entry.hero = 143 := by exact (by intro entry member; cases member)
theorem rowDirection186 : ∀ entry ∈ rowCases186, entry.direction = .east := by exact (by intro entry member; cases member)
theorem rowPhase186 : ∀ entry ∈ rowCases186, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases187 : List PhysicalCase := [case126, case699]
theorem memberCase126 : case126 ∈ rowCases187 := by exact List.mem_cons_self
theorem memberCase699 : case699 ∈ rowCases187 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits187 : ∀ entry ∈ rowCases187, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case126_fitted, (List.forall_mem_cons.mpr ⟨case699_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked187 : ∀ entry ∈ rowCases187, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame126_checked, (List.forall_mem_cons.mpr ⟨frame699_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero187 : ∀ entry ∈ rowCases187, entry.hero = 143 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection187 : ∀ entry ∈ rowCases187, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase187 : ∀ entry ∈ rowCases187, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases188 : List PhysicalCase := []
theorem rowFits188 : ∀ entry ∈ rowCases188, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked188 : ∀ entry ∈ rowCases188, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero188 : ∀ entry ∈ rowCases188, entry.hero = 143 := by exact (by intro entry member; cases member)
theorem rowDirection188 : ∀ entry ∈ rowCases188, entry.direction = .northEast := by exact (by intro entry member; cases member)
theorem rowPhase188 : ∀ entry ∈ rowCases188, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases189 : List PhysicalCase := [case127, case128]
theorem memberCase127 : case127 ∈ rowCases189 := by exact List.mem_cons_self
theorem memberCase128 : case128 ∈ rowCases189 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits189 : ∀ entry ∈ rowCases189, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case127_fitted, (List.forall_mem_cons.mpr ⟨case128_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked189 : ∀ entry ∈ rowCases189, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame127_checked, (List.forall_mem_cons.mpr ⟨frame128_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero189 : ∀ entry ∈ rowCases189, entry.hero = 143 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection189 : ∀ entry ∈ rowCases189, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase189 : ∀ entry ∈ rowCases189, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases190 : List PhysicalCase := []
theorem rowFits190 : ∀ entry ∈ rowCases190, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked190 : ∀ entry ∈ rowCases190, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero190 : ∀ entry ∈ rowCases190, entry.hero = 143 := by exact (by intro entry member; cases member)
theorem rowDirection190 : ∀ entry ∈ rowCases190, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase190 : ∀ entry ∈ rowCases190, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases191 : List PhysicalCase := [case129, case130]
theorem memberCase129 : case129 ∈ rowCases191 := by exact List.mem_cons_self
theorem memberCase130 : case130 ∈ rowCases191 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits191 : ∀ entry ∈ rowCases191, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case129_fitted, (List.forall_mem_cons.mpr ⟨case130_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked191 : ∀ entry ∈ rowCases191, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame129_checked, (List.forall_mem_cons.mpr ⟨frame130_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero191 : ∀ entry ∈ rowCases191, entry.hero = 143 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection191 : ∀ entry ∈ rowCases191, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase191 : ∀ entry ∈ rowCases191, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases192 : List PhysicalCase := [case131, case680]
theorem memberCase131 : case131 ∈ rowCases192 := by exact List.mem_cons_self
theorem memberCase680 : case680 ∈ rowCases192 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits192 : ∀ entry ∈ rowCases192, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case131_fitted, (List.forall_mem_cons.mpr ⟨case680_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked192 : ∀ entry ∈ rowCases192, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame131_checked, (List.forall_mem_cons.mpr ⟨frame680_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero192 : ∀ entry ∈ rowCases192, entry.hero = 157 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection192 : ∀ entry ∈ rowCases192, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase192 : ∀ entry ∈ rowCases192, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases193 : List PhysicalCase := []
theorem rowFits193 : ∀ entry ∈ rowCases193, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked193 : ∀ entry ∈ rowCases193, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero193 : ∀ entry ∈ rowCases193, entry.hero = 157 := by exact (by intro entry member; cases member)
theorem rowDirection193 : ∀ entry ∈ rowCases193, entry.direction = .south := by exact (by intro entry member; cases member)
theorem rowPhase193 : ∀ entry ∈ rowCases193, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases194 : List PhysicalCase := [case132, case704]
theorem memberCase132 : case132 ∈ rowCases194 := by exact List.mem_cons_self
theorem memberCase704 : case704 ∈ rowCases194 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits194 : ∀ entry ∈ rowCases194, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case132_fitted, (List.forall_mem_cons.mpr ⟨case704_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked194 : ∀ entry ∈ rowCases194, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame132_checked, (List.forall_mem_cons.mpr ⟨frame704_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero194 : ∀ entry ∈ rowCases194, entry.hero = 157 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection194 : ∀ entry ∈ rowCases194, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase194 : ∀ entry ∈ rowCases194, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases195 : List PhysicalCase := []
theorem rowFits195 : ∀ entry ∈ rowCases195, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked195 : ∀ entry ∈ rowCases195, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero195 : ∀ entry ∈ rowCases195, entry.hero = 157 := by exact (by intro entry member; cases member)
theorem rowDirection195 : ∀ entry ∈ rowCases195, entry.direction = .west := by exact (by intro entry member; cases member)
theorem rowPhase195 : ∀ entry ∈ rowCases195, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases196 : List PhysicalCase := [case133, case134]
theorem memberCase133 : case133 ∈ rowCases196 := by exact List.mem_cons_self
theorem memberCase134 : case134 ∈ rowCases196 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits196 : ∀ entry ∈ rowCases196, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case133_fitted, (List.forall_mem_cons.mpr ⟨case134_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked196 : ∀ entry ∈ rowCases196, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame133_checked, (List.forall_mem_cons.mpr ⟨frame134_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero196 : ∀ entry ∈ rowCases196, entry.hero = 157 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection196 : ∀ entry ∈ rowCases196, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase196 : ∀ entry ∈ rowCases196, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases197 : List PhysicalCase := []
theorem rowFits197 : ∀ entry ∈ rowCases197, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked197 : ∀ entry ∈ rowCases197, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero197 : ∀ entry ∈ rowCases197, entry.hero = 157 := by exact (by intro entry member; cases member)
theorem rowDirection197 : ∀ entry ∈ rowCases197, entry.direction = .northWest := by exact (by intro entry member; cases member)
theorem rowPhase197 : ∀ entry ∈ rowCases197, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases198 : List PhysicalCase := [case135]
theorem memberCase135 : case135 ∈ rowCases198 := by exact List.mem_cons_self
theorem rowFits198 : ∀ entry ∈ rowCases198, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case135_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked198 : ∀ entry ∈ rowCases198, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame135_checked, (by intro entry member; cases member)⟩)
theorem rowHero198 : ∀ entry ∈ rowCases198, entry.hero = 157 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection198 : ∀ entry ∈ rowCases198, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase198 : ∀ entry ∈ rowCases198, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases199 : List PhysicalCase := []
theorem rowFits199 : ∀ entry ∈ rowCases199, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked199 : ∀ entry ∈ rowCases199, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero199 : ∀ entry ∈ rowCases199, entry.hero = 157 := by exact (by intro entry member; cases member)
theorem rowDirection199 : ∀ entry ∈ rowCases199, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase199 : ∀ entry ∈ rowCases199, entry.phase = 3 := by exact (by intro entry member; cases member)
end NetHack.Soko12Forward220.Unified.P03
