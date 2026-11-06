import NetHack.Soko12Forward220.Unified.P04.OracleCases01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P04
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
noncomputable def rowCases100 : List PhysicalCase := []
theorem rowFits100 : ∀ entry ∈ rowCases100, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked100 : ∀ entry ∈ rowCases100, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero100 : ∀ entry ∈ rowCases100, entry.hero = 108 := by exact (by intro entry member; cases member)
theorem rowDirection100 : ∀ entry ∈ rowCases100, entry.direction = .northEast := by exact (by intro entry member; cases member)
theorem rowPhase100 : ∀ entry ∈ rowCases100, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases101 : List PhysicalCase := []
theorem rowFits101 : ∀ entry ∈ rowCases101, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked101 : ∀ entry ∈ rowCases101, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero101 : ∀ entry ∈ rowCases101, entry.hero = 108 := by exact (by intro entry member; cases member)
theorem rowDirection101 : ∀ entry ∈ rowCases101, entry.direction = .northWest := by exact (by intro entry member; cases member)
theorem rowPhase101 : ∀ entry ∈ rowCases101, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases102 : List PhysicalCase := [case042]
theorem memberCase042 : case042 ∈ rowCases102 := by exact List.mem_cons_self
theorem rowFits102 : ∀ entry ∈ rowCases102, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case042_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked102 : ∀ entry ∈ rowCases102, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame042_checked, (by intro entry member; cases member)⟩)
theorem rowHero102 : ∀ entry ∈ rowCases102, entry.hero = 108 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection102 : ∀ entry ∈ rowCases102, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase102 : ∀ entry ∈ rowCases102, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases103 : List PhysicalCase := [case043]
theorem memberCase043 : case043 ∈ rowCases103 := by exact List.mem_cons_self
theorem rowFits103 : ∀ entry ∈ rowCases103, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case043_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked103 : ∀ entry ∈ rowCases103, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame043_checked, (by intro entry member; cases member)⟩)
theorem rowHero103 : ∀ entry ∈ rowCases103, entry.hero = 108 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection103 : ∀ entry ∈ rowCases103, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase103 : ∀ entry ∈ rowCases103, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases104 : List PhysicalCase := []
theorem rowFits104 : ∀ entry ∈ rowCases104, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked104 : ∀ entry ∈ rowCases104, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero104 : ∀ entry ∈ rowCases104, entry.hero = 115 := by exact (by intro entry member; cases member)
theorem rowDirection104 : ∀ entry ∈ rowCases104, entry.direction = .north := by exact (by intro entry member; cases member)
theorem rowPhase104 : ∀ entry ∈ rowCases104, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases105 : List PhysicalCase := [case044, case695]
theorem memberCase044 : case044 ∈ rowCases105 := by exact List.mem_cons_self
theorem memberCase695 : case695 ∈ rowCases105 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits105 : ∀ entry ∈ rowCases105, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case044_fitted, (List.forall_mem_cons.mpr ⟨case695_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked105 : ∀ entry ∈ rowCases105, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame044_checked, (List.forall_mem_cons.mpr ⟨frame695_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero105 : ∀ entry ∈ rowCases105, entry.hero = 115 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection105 : ∀ entry ∈ rowCases105, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase105 : ∀ entry ∈ rowCases105, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases106 : List PhysicalCase := [case045, case680]
theorem memberCase045 : case045 ∈ rowCases106 := by exact List.mem_cons_self
theorem memberCase680 : case680 ∈ rowCases106 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits106 : ∀ entry ∈ rowCases106, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case045_fitted, (List.forall_mem_cons.mpr ⟨case680_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked106 : ∀ entry ∈ rowCases106, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame045_checked, (List.forall_mem_cons.mpr ⟨frame680_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero106 : ∀ entry ∈ rowCases106, entry.hero = 115 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection106 : ∀ entry ∈ rowCases106, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase106 : ∀ entry ∈ rowCases106, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases107 : List PhysicalCase := []
theorem rowFits107 : ∀ entry ∈ rowCases107, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked107 : ∀ entry ∈ rowCases107, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero107 : ∀ entry ∈ rowCases107, entry.hero = 115 := by exact (by intro entry member; cases member)
theorem rowDirection107 : ∀ entry ∈ rowCases107, entry.direction = .west := by exact (by intro entry member; cases member)
theorem rowPhase107 : ∀ entry ∈ rowCases107, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases108 : List PhysicalCase := []
theorem rowFits108 : ∀ entry ∈ rowCases108, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked108 : ∀ entry ∈ rowCases108, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero108 : ∀ entry ∈ rowCases108, entry.hero = 115 := by exact (by intro entry member; cases member)
theorem rowDirection108 : ∀ entry ∈ rowCases108, entry.direction = .northEast := by exact (by intro entry member; cases member)
theorem rowPhase108 : ∀ entry ∈ rowCases108, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases109 : List PhysicalCase := []
theorem rowFits109 : ∀ entry ∈ rowCases109, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked109 : ∀ entry ∈ rowCases109, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero109 : ∀ entry ∈ rowCases109, entry.hero = 115 := by exact (by intro entry member; cases member)
theorem rowDirection109 : ∀ entry ∈ rowCases109, entry.direction = .northWest := by exact (by intro entry member; cases member)
theorem rowPhase109 : ∀ entry ∈ rowCases109, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases110 : List PhysicalCase := [case046, case047]
theorem memberCase046 : case046 ∈ rowCases110 := by exact List.mem_cons_self
theorem memberCase047 : case047 ∈ rowCases110 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits110 : ∀ entry ∈ rowCases110, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case046_fitted, (List.forall_mem_cons.mpr ⟨case047_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked110 : ∀ entry ∈ rowCases110, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame046_checked, (List.forall_mem_cons.mpr ⟨frame047_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero110 : ∀ entry ∈ rowCases110, entry.hero = 115 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection110 : ∀ entry ∈ rowCases110, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase110 : ∀ entry ∈ rowCases110, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases111 : List PhysicalCase := [case048]
theorem memberCase048 : case048 ∈ rowCases111 := by exact List.mem_cons_self
theorem rowFits111 : ∀ entry ∈ rowCases111, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case048_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked111 : ∀ entry ∈ rowCases111, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame048_checked, (by intro entry member; cases member)⟩)
theorem rowHero111 : ∀ entry ∈ rowCases111, entry.hero = 115 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection111 : ∀ entry ∈ rowCases111, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase111 : ∀ entry ∈ rowCases111, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases112 : List PhysicalCase := []
theorem rowFits112 : ∀ entry ∈ rowCases112, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked112 : ∀ entry ∈ rowCases112, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero112 : ∀ entry ∈ rowCases112, entry.hero = 116 := by exact (by intro entry member; cases member)
theorem rowDirection112 : ∀ entry ∈ rowCases112, entry.direction = .north := by exact (by intro entry member; cases member)
theorem rowPhase112 : ∀ entry ∈ rowCases112, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases113 : List PhysicalCase := [case049, case699]
theorem memberCase049 : case049 ∈ rowCases113 := by exact List.mem_cons_self
theorem memberCase699 : case699 ∈ rowCases113 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits113 : ∀ entry ∈ rowCases113, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case049_fitted, (List.forall_mem_cons.mpr ⟨case699_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked113 : ∀ entry ∈ rowCases113, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame049_checked, (List.forall_mem_cons.mpr ⟨frame699_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero113 : ∀ entry ∈ rowCases113, entry.hero = 116 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection113 : ∀ entry ∈ rowCases113, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase113 : ∀ entry ∈ rowCases113, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases114 : List PhysicalCase := [case050]
theorem memberCase050 : case050 ∈ rowCases114 := by exact List.mem_cons_self
theorem rowFits114 : ∀ entry ∈ rowCases114, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case050_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked114 : ∀ entry ∈ rowCases114, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame050_checked, (by intro entry member; cases member)⟩)
theorem rowHero114 : ∀ entry ∈ rowCases114, entry.hero = 116 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection114 : ∀ entry ∈ rowCases114, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase114 : ∀ entry ∈ rowCases114, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases115 : List PhysicalCase := [case051]
theorem memberCase051 : case051 ∈ rowCases115 := by exact List.mem_cons_self
theorem rowFits115 : ∀ entry ∈ rowCases115, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case051_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked115 : ∀ entry ∈ rowCases115, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame051_checked, (by intro entry member; cases member)⟩)
theorem rowHero115 : ∀ entry ∈ rowCases115, entry.hero = 116 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection115 : ∀ entry ∈ rowCases115, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase115 : ∀ entry ∈ rowCases115, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases116 : List PhysicalCase := []
theorem rowFits116 : ∀ entry ∈ rowCases116, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked116 : ∀ entry ∈ rowCases116, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero116 : ∀ entry ∈ rowCases116, entry.hero = 116 := by exact (by intro entry member; cases member)
theorem rowDirection116 : ∀ entry ∈ rowCases116, entry.direction = .northEast := by exact (by intro entry member; cases member)
theorem rowPhase116 : ∀ entry ∈ rowCases116, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases117 : List PhysicalCase := []
theorem rowFits117 : ∀ entry ∈ rowCases117, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked117 : ∀ entry ∈ rowCases117, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero117 : ∀ entry ∈ rowCases117, entry.hero = 116 := by exact (by intro entry member; cases member)
theorem rowDirection117 : ∀ entry ∈ rowCases117, entry.direction = .northWest := by exact (by intro entry member; cases member)
theorem rowPhase117 : ∀ entry ∈ rowCases117, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases118 : List PhysicalCase := [case052, case053]
theorem memberCase052 : case052 ∈ rowCases118 := by exact List.mem_cons_self
theorem memberCase053 : case053 ∈ rowCases118 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits118 : ∀ entry ∈ rowCases118, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case052_fitted, (List.forall_mem_cons.mpr ⟨case053_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked118 : ∀ entry ∈ rowCases118, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame052_checked, (List.forall_mem_cons.mpr ⟨frame053_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero118 : ∀ entry ∈ rowCases118, entry.hero = 116 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection118 : ∀ entry ∈ rowCases118, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase118 : ∀ entry ∈ rowCases118, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases119 : List PhysicalCase := [case054, case055]
theorem memberCase054 : case054 ∈ rowCases119 := by exact List.mem_cons_self
theorem memberCase055 : case055 ∈ rowCases119 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits119 : ∀ entry ∈ rowCases119, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case054_fitted, (List.forall_mem_cons.mpr ⟨case055_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked119 : ∀ entry ∈ rowCases119, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame054_checked, (List.forall_mem_cons.mpr ⟨frame055_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero119 : ∀ entry ∈ rowCases119, entry.hero = 116 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection119 : ∀ entry ∈ rowCases119, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase119 : ∀ entry ∈ rowCases119, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases120 : List PhysicalCase := []
theorem rowFits120 : ∀ entry ∈ rowCases120, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked120 : ∀ entry ∈ rowCases120, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero120 : ∀ entry ∈ rowCases120, entry.hero = 117 := by exact (by intro entry member; cases member)
theorem rowDirection120 : ∀ entry ∈ rowCases120, entry.direction = .north := by exact (by intro entry member; cases member)
theorem rowPhase120 : ∀ entry ∈ rowCases120, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases121 : List PhysicalCase := [case056, case703]
theorem memberCase056 : case056 ∈ rowCases121 := by exact List.mem_cons_self
theorem memberCase703 : case703 ∈ rowCases121 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits121 : ∀ entry ∈ rowCases121, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case056_fitted, (List.forall_mem_cons.mpr ⟨case703_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked121 : ∀ entry ∈ rowCases121, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame056_checked, (List.forall_mem_cons.mpr ⟨frame703_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero121 : ∀ entry ∈ rowCases121, entry.hero = 117 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection121 : ∀ entry ∈ rowCases121, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase121 : ∀ entry ∈ rowCases121, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases122 : List PhysicalCase := []
theorem rowFits122 : ∀ entry ∈ rowCases122, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked122 : ∀ entry ∈ rowCases122, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero122 : ∀ entry ∈ rowCases122, entry.hero = 117 := by exact (by intro entry member; cases member)
theorem rowDirection122 : ∀ entry ∈ rowCases122, entry.direction = .east := by exact (by intro entry member; cases member)
theorem rowPhase122 : ∀ entry ∈ rowCases122, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases123 : List PhysicalCase := [case057, case681]
theorem memberCase057 : case057 ∈ rowCases123 := by exact List.mem_cons_self
theorem memberCase681 : case681 ∈ rowCases123 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits123 : ∀ entry ∈ rowCases123, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case057_fitted, (List.forall_mem_cons.mpr ⟨case681_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked123 : ∀ entry ∈ rowCases123, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame057_checked, (List.forall_mem_cons.mpr ⟨frame681_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero123 : ∀ entry ∈ rowCases123, entry.hero = 117 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection123 : ∀ entry ∈ rowCases123, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase123 : ∀ entry ∈ rowCases123, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases124 : List PhysicalCase := []
theorem rowFits124 : ∀ entry ∈ rowCases124, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked124 : ∀ entry ∈ rowCases124, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero124 : ∀ entry ∈ rowCases124, entry.hero = 117 := by exact (by intro entry member; cases member)
theorem rowDirection124 : ∀ entry ∈ rowCases124, entry.direction = .northEast := by exact (by intro entry member; cases member)
theorem rowPhase124 : ∀ entry ∈ rowCases124, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases125 : List PhysicalCase := []
theorem rowFits125 : ∀ entry ∈ rowCases125, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked125 : ∀ entry ∈ rowCases125, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero125 : ∀ entry ∈ rowCases125, entry.hero = 117 := by exact (by intro entry member; cases member)
theorem rowDirection125 : ∀ entry ∈ rowCases125, entry.direction = .northWest := by exact (by intro entry member; cases member)
theorem rowPhase125 : ∀ entry ∈ rowCases125, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases126 : List PhysicalCase := []
theorem rowFits126 : ∀ entry ∈ rowCases126, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked126 : ∀ entry ∈ rowCases126, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero126 : ∀ entry ∈ rowCases126, entry.hero = 117 := by exact (by intro entry member; cases member)
theorem rowDirection126 : ∀ entry ∈ rowCases126, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase126 : ∀ entry ∈ rowCases126, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases127 : List PhysicalCase := [case058, case059]
theorem memberCase058 : case058 ∈ rowCases127 := by exact List.mem_cons_self
theorem memberCase059 : case059 ∈ rowCases127 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits127 : ∀ entry ∈ rowCases127, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case058_fitted, (List.forall_mem_cons.mpr ⟨case059_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked127 : ∀ entry ∈ rowCases127, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame058_checked, (List.forall_mem_cons.mpr ⟨frame059_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero127 : ∀ entry ∈ rowCases127, entry.hero = 117 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection127 : ∀ entry ∈ rowCases127, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase127 : ∀ entry ∈ rowCases127, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases128 : List PhysicalCase := [case060]
theorem memberCase060 : case060 ∈ rowCases128 := by exact List.mem_cons_self
theorem rowFits128 : ∀ entry ∈ rowCases128, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case060_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked128 : ∀ entry ∈ rowCases128, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame060_checked, (by intro entry member; cases member)⟩)
theorem rowHero128 : ∀ entry ∈ rowCases128, entry.hero = 131 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection128 : ∀ entry ∈ rowCases128, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase128 : ∀ entry ∈ rowCases128, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases129 : List PhysicalCase := [case061]
theorem memberCase061 : case061 ∈ rowCases129 := by exact List.mem_cons_self
theorem rowFits129 : ∀ entry ∈ rowCases129, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case061_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked129 : ∀ entry ∈ rowCases129, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame061_checked, (by intro entry member; cases member)⟩)
theorem rowHero129 : ∀ entry ∈ rowCases129, entry.hero = 131 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection129 : ∀ entry ∈ rowCases129, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase129 : ∀ entry ∈ rowCases129, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases130 : List PhysicalCase := [case062, case686]
theorem memberCase062 : case062 ∈ rowCases130 := by exact List.mem_cons_self
theorem memberCase686 : case686 ∈ rowCases130 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits130 : ∀ entry ∈ rowCases130, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case062_fitted, (List.forall_mem_cons.mpr ⟨case686_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked130 : ∀ entry ∈ rowCases130, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame062_checked, (List.forall_mem_cons.mpr ⟨frame686_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero130 : ∀ entry ∈ rowCases130, entry.hero = 131 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection130 : ∀ entry ∈ rowCases130, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase130 : ∀ entry ∈ rowCases130, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases131 : List PhysicalCase := []
theorem rowFits131 : ∀ entry ∈ rowCases131, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked131 : ∀ entry ∈ rowCases131, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero131 : ∀ entry ∈ rowCases131, entry.hero = 131 := by exact (by intro entry member; cases member)
theorem rowDirection131 : ∀ entry ∈ rowCases131, entry.direction = .west := by exact (by intro entry member; cases member)
theorem rowPhase131 : ∀ entry ∈ rowCases131, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases132 : List PhysicalCase := [case063, case064]
theorem memberCase063 : case063 ∈ rowCases132 := by exact List.mem_cons_self
theorem memberCase064 : case064 ∈ rowCases132 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits132 : ∀ entry ∈ rowCases132, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case063_fitted, (List.forall_mem_cons.mpr ⟨case064_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked132 : ∀ entry ∈ rowCases132, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame063_checked, (List.forall_mem_cons.mpr ⟨frame064_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero132 : ∀ entry ∈ rowCases132, entry.hero = 131 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection132 : ∀ entry ∈ rowCases132, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase132 : ∀ entry ∈ rowCases132, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases133 : List PhysicalCase := []
theorem rowFits133 : ∀ entry ∈ rowCases133, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked133 : ∀ entry ∈ rowCases133, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero133 : ∀ entry ∈ rowCases133, entry.hero = 131 := by exact (by intro entry member; cases member)
theorem rowDirection133 : ∀ entry ∈ rowCases133, entry.direction = .northWest := by exact (by intro entry member; cases member)
theorem rowPhase133 : ∀ entry ∈ rowCases133, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases134 : List PhysicalCase := [case065, case066]
theorem memberCase065 : case065 ∈ rowCases134 := by exact List.mem_cons_self
theorem memberCase066 : case066 ∈ rowCases134 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits134 : ∀ entry ∈ rowCases134, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case065_fitted, (List.forall_mem_cons.mpr ⟨case066_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked134 : ∀ entry ∈ rowCases134, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame065_checked, (List.forall_mem_cons.mpr ⟨frame066_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero134 : ∀ entry ∈ rowCases134, entry.hero = 131 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection134 : ∀ entry ∈ rowCases134, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase134 : ∀ entry ∈ rowCases134, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases135 : List PhysicalCase := []
theorem rowFits135 : ∀ entry ∈ rowCases135, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked135 : ∀ entry ∈ rowCases135, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero135 : ∀ entry ∈ rowCases135, entry.hero = 131 := by exact (by intro entry member; cases member)
theorem rowDirection135 : ∀ entry ∈ rowCases135, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase135 : ∀ entry ∈ rowCases135, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases136 : List PhysicalCase := [case067]
theorem memberCase067 : case067 ∈ rowCases136 := by exact List.mem_cons_self
theorem rowFits136 : ∀ entry ∈ rowCases136, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case067_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked136 : ∀ entry ∈ rowCases136, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame067_checked, (by intro entry member; cases member)⟩)
theorem rowHero136 : ∀ entry ∈ rowCases136, entry.hero = 132 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection136 : ∀ entry ∈ rowCases136, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase136 : ∀ entry ∈ rowCases136, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases137 : List PhysicalCase := [case068, case705]
theorem memberCase068 : case068 ∈ rowCases137 := by exact List.mem_cons_self
theorem memberCase705 : case705 ∈ rowCases137 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits137 : ∀ entry ∈ rowCases137, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case068_fitted, (List.forall_mem_cons.mpr ⟨case705_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked137 : ∀ entry ∈ rowCases137, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame068_checked, (List.forall_mem_cons.mpr ⟨frame705_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero137 : ∀ entry ∈ rowCases137, entry.hero = 132 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection137 : ∀ entry ∈ rowCases137, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase137 : ∀ entry ∈ rowCases137, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases138 : List PhysicalCase := [case069, case688]
theorem memberCase069 : case069 ∈ rowCases138 := by exact List.mem_cons_self
theorem memberCase688 : case688 ∈ rowCases138 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits138 : ∀ entry ∈ rowCases138, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case069_fitted, (List.forall_mem_cons.mpr ⟨case688_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked138 : ∀ entry ∈ rowCases138, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame069_checked, (List.forall_mem_cons.mpr ⟨frame688_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero138 : ∀ entry ∈ rowCases138, entry.hero = 132 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection138 : ∀ entry ∈ rowCases138, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase138 : ∀ entry ∈ rowCases138, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases139 : List PhysicalCase := [case070]
theorem memberCase070 : case070 ∈ rowCases139 := by exact List.mem_cons_self
theorem rowFits139 : ∀ entry ∈ rowCases139, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case070_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked139 : ∀ entry ∈ rowCases139, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame070_checked, (by intro entry member; cases member)⟩)
theorem rowHero139 : ∀ entry ∈ rowCases139, entry.hero = 132 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection139 : ∀ entry ∈ rowCases139, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase139 : ∀ entry ∈ rowCases139, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases140 : List PhysicalCase := []
theorem rowFits140 : ∀ entry ∈ rowCases140, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked140 : ∀ entry ∈ rowCases140, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero140 : ∀ entry ∈ rowCases140, entry.hero = 132 := by exact (by intro entry member; cases member)
theorem rowDirection140 : ∀ entry ∈ rowCases140, entry.direction = .northEast := by exact (by intro entry member; cases member)
theorem rowPhase140 : ∀ entry ∈ rowCases140, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases141 : List PhysicalCase := [case071, case072]
theorem memberCase071 : case071 ∈ rowCases141 := by exact List.mem_cons_self
theorem memberCase072 : case072 ∈ rowCases141 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits141 : ∀ entry ∈ rowCases141, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case071_fitted, (List.forall_mem_cons.mpr ⟨case072_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked141 : ∀ entry ∈ rowCases141, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame071_checked, (List.forall_mem_cons.mpr ⟨frame072_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero141 : ∀ entry ∈ rowCases141, entry.hero = 132 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection141 : ∀ entry ∈ rowCases141, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase141 : ∀ entry ∈ rowCases141, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases142 : List PhysicalCase := [case073, case074]
theorem memberCase073 : case073 ∈ rowCases142 := by exact List.mem_cons_self
theorem memberCase074 : case074 ∈ rowCases142 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits142 : ∀ entry ∈ rowCases142, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case073_fitted, (List.forall_mem_cons.mpr ⟨case074_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked142 : ∀ entry ∈ rowCases142, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame073_checked, (List.forall_mem_cons.mpr ⟨frame074_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero142 : ∀ entry ∈ rowCases142, entry.hero = 132 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection142 : ∀ entry ∈ rowCases142, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase142 : ∀ entry ∈ rowCases142, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases143 : List PhysicalCase := [case075, case076]
theorem memberCase075 : case075 ∈ rowCases143 := by exact List.mem_cons_self
theorem memberCase076 : case076 ∈ rowCases143 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits143 : ∀ entry ∈ rowCases143, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case075_fitted, (List.forall_mem_cons.mpr ⟨case076_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked143 : ∀ entry ∈ rowCases143, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame075_checked, (List.forall_mem_cons.mpr ⟨frame076_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero143 : ∀ entry ∈ rowCases143, entry.hero = 132 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection143 : ∀ entry ∈ rowCases143, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase143 : ∀ entry ∈ rowCases143, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases144 : List PhysicalCase := []
theorem rowFits144 : ∀ entry ∈ rowCases144, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked144 : ∀ entry ∈ rowCases144, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero144 : ∀ entry ∈ rowCases144, entry.hero = 133 := by exact (by intro entry member; cases member)
theorem rowDirection144 : ∀ entry ∈ rowCases144, entry.direction = .north := by exact (by intro entry member; cases member)
theorem rowPhase144 : ∀ entry ∈ rowCases144, entry.phase = 4 := by exact (by intro entry member; cases member)
noncomputable def rowCases145 : List PhysicalCase := [case077, case709]
theorem memberCase077 : case077 ∈ rowCases145 := by exact List.mem_cons_self
theorem memberCase709 : case709 ∈ rowCases145 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits145 : ∀ entry ∈ rowCases145, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case077_fitted, (List.forall_mem_cons.mpr ⟨case709_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked145 : ∀ entry ∈ rowCases145, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame077_checked, (List.forall_mem_cons.mpr ⟨frame709_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero145 : ∀ entry ∈ rowCases145, entry.hero = 133 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection145 : ∀ entry ∈ rowCases145, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase145 : ∀ entry ∈ rowCases145, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases146 : List PhysicalCase := [case078, case692]
theorem memberCase078 : case078 ∈ rowCases146 := by exact List.mem_cons_self
theorem memberCase692 : case692 ∈ rowCases146 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits146 : ∀ entry ∈ rowCases146, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case078_fitted, (List.forall_mem_cons.mpr ⟨case692_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked146 : ∀ entry ∈ rowCases146, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame078_checked, (List.forall_mem_cons.mpr ⟨frame692_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero146 : ∀ entry ∈ rowCases146, entry.hero = 133 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection146 : ∀ entry ∈ rowCases146, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase146 : ∀ entry ∈ rowCases146, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases147 : List PhysicalCase := [case079, case687]
theorem memberCase079 : case079 ∈ rowCases147 := by exact List.mem_cons_self
theorem memberCase687 : case687 ∈ rowCases147 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits147 : ∀ entry ∈ rowCases147, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case079_fitted, (List.forall_mem_cons.mpr ⟨case687_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked147 : ∀ entry ∈ rowCases147, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame079_checked, (List.forall_mem_cons.mpr ⟨frame687_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero147 : ∀ entry ∈ rowCases147, entry.hero = 133 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection147 : ∀ entry ∈ rowCases147, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase147 : ∀ entry ∈ rowCases147, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases148 : List PhysicalCase := [case080]
theorem memberCase080 : case080 ∈ rowCases148 := by exact List.mem_cons_self
theorem rowFits148 : ∀ entry ∈ rowCases148, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case080_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked148 : ∀ entry ∈ rowCases148, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame080_checked, (by intro entry member; cases member)⟩)
theorem rowHero148 : ∀ entry ∈ rowCases148, entry.hero = 133 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection148 : ∀ entry ∈ rowCases148, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase148 : ∀ entry ∈ rowCases148, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases149 : List PhysicalCase := [case081]
theorem memberCase081 : case081 ∈ rowCases149 := by exact List.mem_cons_self
theorem rowFits149 : ∀ entry ∈ rowCases149, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case081_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked149 : ∀ entry ∈ rowCases149, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame081_checked, (by intro entry member; cases member)⟩)
theorem rowHero149 : ∀ entry ∈ rowCases149, entry.hero = 133 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection149 : ∀ entry ∈ rowCases149, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase149 : ∀ entry ∈ rowCases149, entry.phase = 4 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
end NetHack.Soko12Forward220.Unified.P04
