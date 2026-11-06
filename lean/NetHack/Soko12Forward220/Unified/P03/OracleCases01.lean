import NetHack.Soko12Forward220.Unified.P03.OracleCases00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P03
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
noncomputable def rowCases50 : List PhysicalCase := [case017]
theorem memberCase017 : case017 ∈ rowCases50 := by exact List.mem_cons_self
theorem rowFits50 : ∀ entry ∈ rowCases50, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case017_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked50 : ∀ entry ∈ rowCases50, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame017_checked, (by intro entry member; cases member)⟩)
theorem rowHero50 : ∀ entry ∈ rowCases50, entry.hero = 55 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection50 : ∀ entry ∈ rowCases50, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase50 : ∀ entry ∈ rowCases50, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases51 : List PhysicalCase := []
theorem rowFits51 : ∀ entry ∈ rowCases51, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked51 : ∀ entry ∈ rowCases51, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero51 : ∀ entry ∈ rowCases51, entry.hero = 55 := by exact (by intro entry member; cases member)
theorem rowDirection51 : ∀ entry ∈ rowCases51, entry.direction = .west := by exact (by intro entry member; cases member)
theorem rowPhase51 : ∀ entry ∈ rowCases51, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases52 : List PhysicalCase := [case018, case019]
theorem memberCase018 : case018 ∈ rowCases52 := by exact List.mem_cons_self
theorem memberCase019 : case019 ∈ rowCases52 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits52 : ∀ entry ∈ rowCases52, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case018_fitted, (List.forall_mem_cons.mpr ⟨case019_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked52 : ∀ entry ∈ rowCases52, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame018_checked, (List.forall_mem_cons.mpr ⟨frame019_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero52 : ∀ entry ∈ rowCases52, entry.hero = 55 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection52 : ∀ entry ∈ rowCases52, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase52 : ∀ entry ∈ rowCases52, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases53 : List PhysicalCase := []
theorem rowFits53 : ∀ entry ∈ rowCases53, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked53 : ∀ entry ∈ rowCases53, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero53 : ∀ entry ∈ rowCases53, entry.hero = 55 := by exact (by intro entry member; cases member)
theorem rowDirection53 : ∀ entry ∈ rowCases53, entry.direction = .northWest := by exact (by intro entry member; cases member)
theorem rowPhase53 : ∀ entry ∈ rowCases53, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases54 : List PhysicalCase := [case020]
theorem memberCase020 : case020 ∈ rowCases54 := by exact List.mem_cons_self
theorem rowFits54 : ∀ entry ∈ rowCases54, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case020_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked54 : ∀ entry ∈ rowCases54, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame020_checked, (by intro entry member; cases member)⟩)
theorem rowHero54 : ∀ entry ∈ rowCases54, entry.hero = 55 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection54 : ∀ entry ∈ rowCases54, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase54 : ∀ entry ∈ rowCases54, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases55 : List PhysicalCase := []
theorem rowFits55 : ∀ entry ∈ rowCases55, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked55 : ∀ entry ∈ rowCases55, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero55 : ∀ entry ∈ rowCases55, entry.hero = 55 := by exact (by intro entry member; cases member)
theorem rowDirection55 : ∀ entry ∈ rowCases55, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase55 : ∀ entry ∈ rowCases55, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases56 : List PhysicalCase := [case021]
theorem memberCase021 : case021 ∈ rowCases56 := by exact List.mem_cons_self
theorem rowFits56 : ∀ entry ∈ rowCases56, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case021_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked56 : ∀ entry ∈ rowCases56, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame021_checked, (by intro entry member; cases member)⟩)
theorem rowHero56 : ∀ entry ∈ rowCases56, entry.hero = 56 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection56 : ∀ entry ∈ rowCases56, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase56 : ∀ entry ∈ rowCases56, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases57 : List PhysicalCase := [case022, case675]
theorem memberCase022 : case022 ∈ rowCases57 := by exact List.mem_cons_self
theorem memberCase675 : case675 ∈ rowCases57 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits57 : ∀ entry ∈ rowCases57, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case022_fitted, (List.forall_mem_cons.mpr ⟨case675_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked57 : ∀ entry ∈ rowCases57, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame022_checked, (List.forall_mem_cons.mpr ⟨frame675_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero57 : ∀ entry ∈ rowCases57, entry.hero = 56 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection57 : ∀ entry ∈ rowCases57, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase57 : ∀ entry ∈ rowCases57, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases58 : List PhysicalCase := []
theorem rowFits58 : ∀ entry ∈ rowCases58, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked58 : ∀ entry ∈ rowCases58, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero58 : ∀ entry ∈ rowCases58, entry.hero = 56 := by exact (by intro entry member; cases member)
theorem rowDirection58 : ∀ entry ∈ rowCases58, entry.direction = .east := by exact (by intro entry member; cases member)
theorem rowPhase58 : ∀ entry ∈ rowCases58, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases59 : List PhysicalCase := [case023]
theorem memberCase023 : case023 ∈ rowCases59 := by exact List.mem_cons_self
theorem rowFits59 : ∀ entry ∈ rowCases59, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case023_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked59 : ∀ entry ∈ rowCases59, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame023_checked, (by intro entry member; cases member)⟩)
theorem rowHero59 : ∀ entry ∈ rowCases59, entry.hero = 56 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection59 : ∀ entry ∈ rowCases59, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase59 : ∀ entry ∈ rowCases59, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases60 : List PhysicalCase := [case024]
theorem memberCase024 : case024 ∈ rowCases60 := by exact List.mem_cons_self
theorem rowFits60 : ∀ entry ∈ rowCases60, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case024_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked60 : ∀ entry ∈ rowCases60, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame024_checked, (by intro entry member; cases member)⟩)
theorem rowHero60 : ∀ entry ∈ rowCases60, entry.hero = 56 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection60 : ∀ entry ∈ rowCases60, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase60 : ∀ entry ∈ rowCases60, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases61 : List PhysicalCase := [case025]
theorem memberCase025 : case025 ∈ rowCases61 := by exact List.mem_cons_self
theorem rowFits61 : ∀ entry ∈ rowCases61, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case025_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked61 : ∀ entry ∈ rowCases61, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame025_checked, (by intro entry member; cases member)⟩)
theorem rowHero61 : ∀ entry ∈ rowCases61, entry.hero = 56 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection61 : ∀ entry ∈ rowCases61, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase61 : ∀ entry ∈ rowCases61, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases62 : List PhysicalCase := []
theorem rowFits62 : ∀ entry ∈ rowCases62, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked62 : ∀ entry ∈ rowCases62, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero62 : ∀ entry ∈ rowCases62, entry.hero = 56 := by exact (by intro entry member; cases member)
theorem rowDirection62 : ∀ entry ∈ rowCases62, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase62 : ∀ entry ∈ rowCases62, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases63 : List PhysicalCase := []
theorem rowFits63 : ∀ entry ∈ rowCases63, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked63 : ∀ entry ∈ rowCases63, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero63 : ∀ entry ∈ rowCases63, entry.hero = 56 := by exact (by intro entry member; cases member)
theorem rowDirection63 : ∀ entry ∈ rowCases63, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase63 : ∀ entry ∈ rowCases63, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases64 : List PhysicalCase := [case026, case672]
theorem memberCase026 : case026 ∈ rowCases64 := by exact List.mem_cons_self
theorem memberCase672 : case672 ∈ rowCases64 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits64 : ∀ entry ∈ rowCases64, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case026_fitted, (List.forall_mem_cons.mpr ⟨case672_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked64 : ∀ entry ∈ rowCases64, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame026_checked, (List.forall_mem_cons.mpr ⟨frame672_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero64 : ∀ entry ∈ rowCases64, entry.hero = 82 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection64 : ∀ entry ∈ rowCases64, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase64 : ∀ entry ∈ rowCases64, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases65 : List PhysicalCase := [case027, case677]
theorem memberCase027 : case027 ∈ rowCases65 := by exact List.mem_cons_self
theorem memberCase677 : case677 ∈ rowCases65 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits65 : ∀ entry ∈ rowCases65, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case027_fitted, (List.forall_mem_cons.mpr ⟨case677_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked65 : ∀ entry ∈ rowCases65, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame027_checked, (List.forall_mem_cons.mpr ⟨frame677_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero65 : ∀ entry ∈ rowCases65, entry.hero = 82 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection65 : ∀ entry ∈ rowCases65, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase65 : ∀ entry ∈ rowCases65, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases66 : List PhysicalCase := []
theorem rowFits66 : ∀ entry ∈ rowCases66, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked66 : ∀ entry ∈ rowCases66, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero66 : ∀ entry ∈ rowCases66, entry.hero = 82 := by exact (by intro entry member; cases member)
theorem rowDirection66 : ∀ entry ∈ rowCases66, entry.direction = .east := by exact (by intro entry member; cases member)
theorem rowPhase66 : ∀ entry ∈ rowCases66, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases67 : List PhysicalCase := []
theorem rowFits67 : ∀ entry ∈ rowCases67, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked67 : ∀ entry ∈ rowCases67, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero67 : ∀ entry ∈ rowCases67, entry.hero = 82 := by exact (by intro entry member; cases member)
theorem rowDirection67 : ∀ entry ∈ rowCases67, entry.direction = .west := by exact (by intro entry member; cases member)
theorem rowPhase67 : ∀ entry ∈ rowCases67, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases68 : List PhysicalCase := []
theorem rowFits68 : ∀ entry ∈ rowCases68, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked68 : ∀ entry ∈ rowCases68, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero68 : ∀ entry ∈ rowCases68, entry.hero = 82 := by exact (by intro entry member; cases member)
theorem rowDirection68 : ∀ entry ∈ rowCases68, entry.direction = .northEast := by exact (by intro entry member; cases member)
theorem rowPhase68 : ∀ entry ∈ rowCases68, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases69 : List PhysicalCase := [case028]
theorem memberCase028 : case028 ∈ rowCases69 := by exact List.mem_cons_self
theorem rowFits69 : ∀ entry ∈ rowCases69, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case028_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked69 : ∀ entry ∈ rowCases69, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame028_checked, (by intro entry member; cases member)⟩)
theorem rowHero69 : ∀ entry ∈ rowCases69, entry.hero = 82 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection69 : ∀ entry ∈ rowCases69, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase69 : ∀ entry ∈ rowCases69, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases70 : List PhysicalCase := []
theorem rowFits70 : ∀ entry ∈ rowCases70, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked70 : ∀ entry ∈ rowCases70, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero70 : ∀ entry ∈ rowCases70, entry.hero = 82 := by exact (by intro entry member; cases member)
theorem rowDirection70 : ∀ entry ∈ rowCases70, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase70 : ∀ entry ∈ rowCases70, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases71 : List PhysicalCase := []
theorem rowFits71 : ∀ entry ∈ rowCases71, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked71 : ∀ entry ∈ rowCases71, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero71 : ∀ entry ∈ rowCases71, entry.hero = 82 := by exact (by intro entry member; cases member)
theorem rowDirection71 : ∀ entry ∈ rowCases71, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase71 : ∀ entry ∈ rowCases71, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases72 : List PhysicalCase := []
theorem rowFits72 : ∀ entry ∈ rowCases72, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked72 : ∀ entry ∈ rowCases72, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero72 : ∀ entry ∈ rowCases72, entry.hero = 105 := by exact (by intro entry member; cases member)
theorem rowDirection72 : ∀ entry ∈ rowCases72, entry.direction = .north := by exact (by intro entry member; cases member)
theorem rowPhase72 : ∀ entry ∈ rowCases72, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases73 : List PhysicalCase := [case029, case681]
theorem memberCase029 : case029 ∈ rowCases73 := by exact List.mem_cons_self
theorem memberCase681 : case681 ∈ rowCases73 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits73 : ∀ entry ∈ rowCases73, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case029_fitted, (List.forall_mem_cons.mpr ⟨case681_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked73 : ∀ entry ∈ rowCases73, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame029_checked, (List.forall_mem_cons.mpr ⟨frame681_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero73 : ∀ entry ∈ rowCases73, entry.hero = 105 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection73 : ∀ entry ∈ rowCases73, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase73 : ∀ entry ∈ rowCases73, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases74 : List PhysicalCase := [case030]
theorem memberCase030 : case030 ∈ rowCases74 := by exact List.mem_cons_self
theorem rowFits74 : ∀ entry ∈ rowCases74, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case030_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked74 : ∀ entry ∈ rowCases74, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame030_checked, (by intro entry member; cases member)⟩)
theorem rowHero74 : ∀ entry ∈ rowCases74, entry.hero = 105 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection74 : ∀ entry ∈ rowCases74, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase74 : ∀ entry ∈ rowCases74, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases75 : List PhysicalCase := []
theorem rowFits75 : ∀ entry ∈ rowCases75, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked75 : ∀ entry ∈ rowCases75, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero75 : ∀ entry ∈ rowCases75, entry.hero = 105 := by exact (by intro entry member; cases member)
theorem rowDirection75 : ∀ entry ∈ rowCases75, entry.direction = .west := by exact (by intro entry member; cases member)
theorem rowPhase75 : ∀ entry ∈ rowCases75, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases76 : List PhysicalCase := []
theorem rowFits76 : ∀ entry ∈ rowCases76, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked76 : ∀ entry ∈ rowCases76, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero76 : ∀ entry ∈ rowCases76, entry.hero = 105 := by exact (by intro entry member; cases member)
theorem rowDirection76 : ∀ entry ∈ rowCases76, entry.direction = .northEast := by exact (by intro entry member; cases member)
theorem rowPhase76 : ∀ entry ∈ rowCases76, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases77 : List PhysicalCase := []
theorem rowFits77 : ∀ entry ∈ rowCases77, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked77 : ∀ entry ∈ rowCases77, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero77 : ∀ entry ∈ rowCases77, entry.hero = 105 := by exact (by intro entry member; cases member)
theorem rowDirection77 : ∀ entry ∈ rowCases77, entry.direction = .northWest := by exact (by intro entry member; cases member)
theorem rowPhase77 : ∀ entry ∈ rowCases77, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases78 : List PhysicalCase := [case031, case032]
theorem memberCase031 : case031 ∈ rowCases78 := by exact List.mem_cons_self
theorem memberCase032 : case032 ∈ rowCases78 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits78 : ∀ entry ∈ rowCases78, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case031_fitted, (List.forall_mem_cons.mpr ⟨case032_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked78 : ∀ entry ∈ rowCases78, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame031_checked, (List.forall_mem_cons.mpr ⟨frame032_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero78 : ∀ entry ∈ rowCases78, entry.hero = 105 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection78 : ∀ entry ∈ rowCases78, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase78 : ∀ entry ∈ rowCases78, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases79 : List PhysicalCase := []
theorem rowFits79 : ∀ entry ∈ rowCases79, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked79 : ∀ entry ∈ rowCases79, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero79 : ∀ entry ∈ rowCases79, entry.hero = 105 := by exact (by intro entry member; cases member)
theorem rowDirection79 : ∀ entry ∈ rowCases79, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase79 : ∀ entry ∈ rowCases79, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases80 : List PhysicalCase := []
theorem rowFits80 : ∀ entry ∈ rowCases80, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked80 : ∀ entry ∈ rowCases80, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero80 : ∀ entry ∈ rowCases80, entry.hero = 106 := by exact (by intro entry member; cases member)
theorem rowDirection80 : ∀ entry ∈ rowCases80, entry.direction = .north := by exact (by intro entry member; cases member)
theorem rowPhase80 : ∀ entry ∈ rowCases80, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases81 : List PhysicalCase := [case033, case683]
theorem memberCase033 : case033 ∈ rowCases81 := by exact List.mem_cons_self
theorem memberCase683 : case683 ∈ rowCases81 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits81 : ∀ entry ∈ rowCases81, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case033_fitted, (List.forall_mem_cons.mpr ⟨case683_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked81 : ∀ entry ∈ rowCases81, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame033_checked, (List.forall_mem_cons.mpr ⟨frame683_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero81 : ∀ entry ∈ rowCases81, entry.hero = 106 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection81 : ∀ entry ∈ rowCases81, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase81 : ∀ entry ∈ rowCases81, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases82 : List PhysicalCase := []
theorem rowFits82 : ∀ entry ∈ rowCases82, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked82 : ∀ entry ∈ rowCases82, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero82 : ∀ entry ∈ rowCases82, entry.hero = 106 := by exact (by intro entry member; cases member)
theorem rowDirection82 : ∀ entry ∈ rowCases82, entry.direction = .east := by exact (by intro entry member; cases member)
theorem rowPhase82 : ∀ entry ∈ rowCases82, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases83 : List PhysicalCase := [case034]
theorem memberCase034 : case034 ∈ rowCases83 := by exact List.mem_cons_self
theorem rowFits83 : ∀ entry ∈ rowCases83, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case034_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked83 : ∀ entry ∈ rowCases83, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame034_checked, (by intro entry member; cases member)⟩)
theorem rowHero83 : ∀ entry ∈ rowCases83, entry.hero = 106 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection83 : ∀ entry ∈ rowCases83, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase83 : ∀ entry ∈ rowCases83, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases84 : List PhysicalCase := []
theorem rowFits84 : ∀ entry ∈ rowCases84, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked84 : ∀ entry ∈ rowCases84, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero84 : ∀ entry ∈ rowCases84, entry.hero = 106 := by exact (by intro entry member; cases member)
theorem rowDirection84 : ∀ entry ∈ rowCases84, entry.direction = .northEast := by exact (by intro entry member; cases member)
theorem rowPhase84 : ∀ entry ∈ rowCases84, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases85 : List PhysicalCase := []
theorem rowFits85 : ∀ entry ∈ rowCases85, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked85 : ∀ entry ∈ rowCases85, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero85 : ∀ entry ∈ rowCases85, entry.hero = 106 := by exact (by intro entry member; cases member)
theorem rowDirection85 : ∀ entry ∈ rowCases85, entry.direction = .northWest := by exact (by intro entry member; cases member)
theorem rowPhase85 : ∀ entry ∈ rowCases85, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases86 : List PhysicalCase := [case035]
theorem memberCase035 : case035 ∈ rowCases86 := by exact List.mem_cons_self
theorem rowFits86 : ∀ entry ∈ rowCases86, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case035_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked86 : ∀ entry ∈ rowCases86, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame035_checked, (by intro entry member; cases member)⟩)
theorem rowHero86 : ∀ entry ∈ rowCases86, entry.hero = 106 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection86 : ∀ entry ∈ rowCases86, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase86 : ∀ entry ∈ rowCases86, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases87 : List PhysicalCase := [case036, case037]
theorem memberCase036 : case036 ∈ rowCases87 := by exact List.mem_cons_self
theorem memberCase037 : case037 ∈ rowCases87 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits87 : ∀ entry ∈ rowCases87, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case036_fitted, (List.forall_mem_cons.mpr ⟨case037_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked87 : ∀ entry ∈ rowCases87, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame036_checked, (List.forall_mem_cons.mpr ⟨frame037_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero87 : ∀ entry ∈ rowCases87, entry.hero = 106 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection87 : ∀ entry ∈ rowCases87, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase87 : ∀ entry ∈ rowCases87, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases88 : List PhysicalCase := [case038, case674]
theorem memberCase038 : case038 ∈ rowCases88 := by exact List.mem_cons_self
theorem memberCase674 : case674 ∈ rowCases88 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits88 : ∀ entry ∈ rowCases88, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case038_fitted, (List.forall_mem_cons.mpr ⟨case674_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked88 : ∀ entry ∈ rowCases88, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame038_checked, (List.forall_mem_cons.mpr ⟨frame674_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero88 : ∀ entry ∈ rowCases88, entry.hero = 108 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection88 : ∀ entry ∈ rowCases88, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase88 : ∀ entry ∈ rowCases88, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases89 : List PhysicalCase := [case039, case689]
theorem memberCase039 : case039 ∈ rowCases89 := by exact List.mem_cons_self
theorem memberCase689 : case689 ∈ rowCases89 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits89 : ∀ entry ∈ rowCases89, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case039_fitted, (List.forall_mem_cons.mpr ⟨case689_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked89 : ∀ entry ∈ rowCases89, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame039_checked, (List.forall_mem_cons.mpr ⟨frame689_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero89 : ∀ entry ∈ rowCases89, entry.hero = 108 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection89 : ∀ entry ∈ rowCases89, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase89 : ∀ entry ∈ rowCases89, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases90 : List PhysicalCase := []
theorem rowFits90 : ∀ entry ∈ rowCases90, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked90 : ∀ entry ∈ rowCases90, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero90 : ∀ entry ∈ rowCases90, entry.hero = 108 := by exact (by intro entry member; cases member)
theorem rowDirection90 : ∀ entry ∈ rowCases90, entry.direction = .east := by exact (by intro entry member; cases member)
theorem rowPhase90 : ∀ entry ∈ rowCases90, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases91 : List PhysicalCase := []
theorem rowFits91 : ∀ entry ∈ rowCases91, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked91 : ∀ entry ∈ rowCases91, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero91 : ∀ entry ∈ rowCases91, entry.hero = 108 := by exact (by intro entry member; cases member)
theorem rowDirection91 : ∀ entry ∈ rowCases91, entry.direction = .west := by exact (by intro entry member; cases member)
theorem rowPhase91 : ∀ entry ∈ rowCases91, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases92 : List PhysicalCase := []
theorem rowFits92 : ∀ entry ∈ rowCases92, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked92 : ∀ entry ∈ rowCases92, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero92 : ∀ entry ∈ rowCases92, entry.hero = 108 := by exact (by intro entry member; cases member)
theorem rowDirection92 : ∀ entry ∈ rowCases92, entry.direction = .northEast := by exact (by intro entry member; cases member)
theorem rowPhase92 : ∀ entry ∈ rowCases92, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases93 : List PhysicalCase := []
theorem rowFits93 : ∀ entry ∈ rowCases93, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked93 : ∀ entry ∈ rowCases93, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero93 : ∀ entry ∈ rowCases93, entry.hero = 108 := by exact (by intro entry member; cases member)
theorem rowDirection93 : ∀ entry ∈ rowCases93, entry.direction = .northWest := by exact (by intro entry member; cases member)
theorem rowPhase93 : ∀ entry ∈ rowCases93, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases94 : List PhysicalCase := [case040]
theorem memberCase040 : case040 ∈ rowCases94 := by exact List.mem_cons_self
theorem rowFits94 : ∀ entry ∈ rowCases94, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case040_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked94 : ∀ entry ∈ rowCases94, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame040_checked, (by intro entry member; cases member)⟩)
theorem rowHero94 : ∀ entry ∈ rowCases94, entry.hero = 108 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection94 : ∀ entry ∈ rowCases94, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase94 : ∀ entry ∈ rowCases94, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases95 : List PhysicalCase := [case041]
theorem memberCase041 : case041 ∈ rowCases95 := by exact List.mem_cons_self
theorem rowFits95 : ∀ entry ∈ rowCases95, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case041_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked95 : ∀ entry ∈ rowCases95, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame041_checked, (by intro entry member; cases member)⟩)
theorem rowHero95 : ∀ entry ∈ rowCases95, entry.hero = 108 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection95 : ∀ entry ∈ rowCases95, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase95 : ∀ entry ∈ rowCases95, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases96 : List PhysicalCase := []
theorem rowFits96 : ∀ entry ∈ rowCases96, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked96 : ∀ entry ∈ rowCases96, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero96 : ∀ entry ∈ rowCases96, entry.hero = 115 := by exact (by intro entry member; cases member)
theorem rowDirection96 : ∀ entry ∈ rowCases96, entry.direction = .north := by exact (by intro entry member; cases member)
theorem rowPhase96 : ∀ entry ∈ rowCases96, entry.phase = 3 := by exact (by intro entry member; cases member)
noncomputable def rowCases97 : List PhysicalCase := [case042, case693]
theorem memberCase042 : case042 ∈ rowCases97 := by exact List.mem_cons_self
theorem memberCase693 : case693 ∈ rowCases97 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits97 : ∀ entry ∈ rowCases97, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case042_fitted, (List.forall_mem_cons.mpr ⟨case693_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked97 : ∀ entry ∈ rowCases97, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame042_checked, (List.forall_mem_cons.mpr ⟨frame693_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero97 : ∀ entry ∈ rowCases97, entry.hero = 115 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection97 : ∀ entry ∈ rowCases97, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase97 : ∀ entry ∈ rowCases97, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases98 : List PhysicalCase := [case043, case678]
theorem memberCase043 : case043 ∈ rowCases98 := by exact List.mem_cons_self
theorem memberCase678 : case678 ∈ rowCases98 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits98 : ∀ entry ∈ rowCases98, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case043_fitted, (List.forall_mem_cons.mpr ⟨case678_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked98 : ∀ entry ∈ rowCases98, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame043_checked, (List.forall_mem_cons.mpr ⟨frame678_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero98 : ∀ entry ∈ rowCases98, entry.hero = 115 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection98 : ∀ entry ∈ rowCases98, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase98 : ∀ entry ∈ rowCases98, entry.phase = 3 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases99 : List PhysicalCase := []
theorem rowFits99 : ∀ entry ∈ rowCases99, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked99 : ∀ entry ∈ rowCases99, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero99 : ∀ entry ∈ rowCases99, entry.hero = 115 := by exact (by intro entry member; cases member)
theorem rowDirection99 : ∀ entry ∈ rowCases99, entry.direction = .west := by exact (by intro entry member; cases member)
theorem rowPhase99 : ∀ entry ∈ rowCases99, entry.phase = 3 := by exact (by intro entry member; cases member)
end NetHack.Soko12Forward220.Unified.P03
