import NetHack.Soko12Forward220.Unified.P00.OracleCases13
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P00
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
noncomputable def rowCases700 : List PhysicalCase := [case641]
theorem memberCase641 : case641 ∈ rowCases700 := by exact List.mem_cons_self
theorem rowFits700 : ∀ entry ∈ rowCases700, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case641_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked700 : ∀ entry ∈ rowCases700, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame641_checked, (by intro entry member; cases member)⟩)
theorem rowHero700 : ∀ entry ∈ rowCases700, entry.hero = 373 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection700 : ∀ entry ∈ rowCases700, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase700 : ∀ entry ∈ rowCases700, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases701 : List PhysicalCase := []
theorem rowFits701 : ∀ entry ∈ rowCases701, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked701 : ∀ entry ∈ rowCases701, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero701 : ∀ entry ∈ rowCases701, entry.hero = 373 := by exact (by intro entry member; cases member)
theorem rowDirection701 : ∀ entry ∈ rowCases701, entry.direction = .northWest := by exact (by intro entry member; cases member)
theorem rowPhase701 : ∀ entry ∈ rowCases701, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases702 : List PhysicalCase := [case642]
theorem memberCase642 : case642 ∈ rowCases702 := by exact List.mem_cons_self
theorem rowFits702 : ∀ entry ∈ rowCases702, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case642_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked702 : ∀ entry ∈ rowCases702, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame642_checked, (by intro entry member; cases member)⟩)
theorem rowHero702 : ∀ entry ∈ rowCases702, entry.hero = 373 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection702 : ∀ entry ∈ rowCases702, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase702 : ∀ entry ∈ rowCases702, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases703 : List PhysicalCase := []
theorem rowFits703 : ∀ entry ∈ rowCases703, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked703 : ∀ entry ∈ rowCases703, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero703 : ∀ entry ∈ rowCases703, entry.hero = 373 := by exact (by intro entry member; cases member)
theorem rowDirection703 : ∀ entry ∈ rowCases703, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase703 : ∀ entry ∈ rowCases703, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases704 : List PhysicalCase := [case643, case842]
theorem memberCase643 : case643 ∈ rowCases704 := by exact List.mem_cons_self
theorem memberCase842 : case842 ∈ rowCases704 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits704 : ∀ entry ∈ rowCases704, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case643_fitted, (List.forall_mem_cons.mpr ⟨case842_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked704 : ∀ entry ∈ rowCases704, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame643_checked, (List.forall_mem_cons.mpr ⟨frame842_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero704 : ∀ entry ∈ rowCases704, entry.hero = 374 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection704 : ∀ entry ∈ rowCases704, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase704 : ∀ entry ∈ rowCases704, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases705 : List PhysicalCase := [case644]
theorem memberCase644 : case644 ∈ rowCases705 := by exact List.mem_cons_self
theorem rowFits705 : ∀ entry ∈ rowCases705, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case644_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked705 : ∀ entry ∈ rowCases705, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame644_checked, (by intro entry member; cases member)⟩)
theorem rowHero705 : ∀ entry ∈ rowCases705, entry.hero = 374 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection705 : ∀ entry ∈ rowCases705, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase705 : ∀ entry ∈ rowCases705, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases706 : List PhysicalCase := []
theorem rowFits706 : ∀ entry ∈ rowCases706, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked706 : ∀ entry ∈ rowCases706, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero706 : ∀ entry ∈ rowCases706, entry.hero = 374 := by exact (by intro entry member; cases member)
theorem rowDirection706 : ∀ entry ∈ rowCases706, entry.direction = .east := by exact (by intro entry member; cases member)
theorem rowPhase706 : ∀ entry ∈ rowCases706, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases707 : List PhysicalCase := [case645, case851]
theorem memberCase645 : case645 ∈ rowCases707 := by exact List.mem_cons_self
theorem memberCase851 : case851 ∈ rowCases707 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits707 : ∀ entry ∈ rowCases707, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case645_fitted, (List.forall_mem_cons.mpr ⟨case851_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked707 : ∀ entry ∈ rowCases707, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame645_checked, (List.forall_mem_cons.mpr ⟨frame851_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero707 : ∀ entry ∈ rowCases707, entry.hero = 374 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection707 : ∀ entry ∈ rowCases707, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase707 : ∀ entry ∈ rowCases707, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases708 : List PhysicalCase := []
theorem rowFits708 : ∀ entry ∈ rowCases708, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked708 : ∀ entry ∈ rowCases708, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero708 : ∀ entry ∈ rowCases708, entry.hero = 374 := by exact (by intro entry member; cases member)
theorem rowDirection708 : ∀ entry ∈ rowCases708, entry.direction = .northEast := by exact (by intro entry member; cases member)
theorem rowPhase708 : ∀ entry ∈ rowCases708, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases709 : List PhysicalCase := []
theorem rowFits709 : ∀ entry ∈ rowCases709, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked709 : ∀ entry ∈ rowCases709, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero709 : ∀ entry ∈ rowCases709, entry.hero = 374 := by exact (by intro entry member; cases member)
theorem rowDirection709 : ∀ entry ∈ rowCases709, entry.direction = .northWest := by exact (by intro entry member; cases member)
theorem rowPhase709 : ∀ entry ∈ rowCases709, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases710 : List PhysicalCase := []
theorem rowFits710 : ∀ entry ∈ rowCases710, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked710 : ∀ entry ∈ rowCases710, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero710 : ∀ entry ∈ rowCases710, entry.hero = 374 := by exact (by intro entry member; cases member)
theorem rowDirection710 : ∀ entry ∈ rowCases710, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase710 : ∀ entry ∈ rowCases710, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases711 : List PhysicalCase := [case646, case647]
theorem memberCase646 : case646 ∈ rowCases711 := by exact List.mem_cons_self
theorem memberCase647 : case647 ∈ rowCases711 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits711 : ∀ entry ∈ rowCases711, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case646_fitted, (List.forall_mem_cons.mpr ⟨case647_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked711 : ∀ entry ∈ rowCases711, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame646_checked, (List.forall_mem_cons.mpr ⟨frame647_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero711 : ∀ entry ∈ rowCases711, entry.hero = 374 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection711 : ∀ entry ∈ rowCases711, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase711 : ∀ entry ∈ rowCases711, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases712 : List PhysicalCase := [case648]
theorem memberCase648 : case648 ∈ rowCases712 := by exact List.mem_cons_self
theorem rowFits712 : ∀ entry ∈ rowCases712, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case648_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked712 : ∀ entry ∈ rowCases712, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame648_checked, (by intro entry member; cases member)⟩)
theorem rowHero712 : ∀ entry ∈ rowCases712, entry.hero = 396 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection712 : ∀ entry ∈ rowCases712, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase712 : ∀ entry ∈ rowCases712, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases713 : List PhysicalCase := []
theorem rowFits713 : ∀ entry ∈ rowCases713, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked713 : ∀ entry ∈ rowCases713, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero713 : ∀ entry ∈ rowCases713, entry.hero = 396 := by exact (by intro entry member; cases member)
theorem rowDirection713 : ∀ entry ∈ rowCases713, entry.direction = .south := by exact (by intro entry member; cases member)
theorem rowPhase713 : ∀ entry ∈ rowCases713, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases714 : List PhysicalCase := [case649]
theorem memberCase649 : case649 ∈ rowCases714 := by exact List.mem_cons_self
theorem rowFits714 : ∀ entry ∈ rowCases714, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case649_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked714 : ∀ entry ∈ rowCases714, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame649_checked, (by intro entry member; cases member)⟩)
theorem rowHero714 : ∀ entry ∈ rowCases714, entry.hero = 396 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection714 : ∀ entry ∈ rowCases714, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase714 : ∀ entry ∈ rowCases714, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases715 : List PhysicalCase := []
theorem rowFits715 : ∀ entry ∈ rowCases715, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked715 : ∀ entry ∈ rowCases715, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero715 : ∀ entry ∈ rowCases715, entry.hero = 396 := by exact (by intro entry member; cases member)
theorem rowDirection715 : ∀ entry ∈ rowCases715, entry.direction = .west := by exact (by intro entry member; cases member)
theorem rowPhase715 : ∀ entry ∈ rowCases715, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases716 : List PhysicalCase := [case650, case651]
theorem memberCase650 : case650 ∈ rowCases716 := by exact List.mem_cons_self
theorem memberCase651 : case651 ∈ rowCases716 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits716 : ∀ entry ∈ rowCases716, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case650_fitted, (List.forall_mem_cons.mpr ⟨case651_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked716 : ∀ entry ∈ rowCases716, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame650_checked, (List.forall_mem_cons.mpr ⟨frame651_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero716 : ∀ entry ∈ rowCases716, entry.hero = 396 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection716 : ∀ entry ∈ rowCases716, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase716 : ∀ entry ∈ rowCases716, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases717 : List PhysicalCase := []
theorem rowFits717 : ∀ entry ∈ rowCases717, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked717 : ∀ entry ∈ rowCases717, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero717 : ∀ entry ∈ rowCases717, entry.hero = 396 := by exact (by intro entry member; cases member)
theorem rowDirection717 : ∀ entry ∈ rowCases717, entry.direction = .northWest := by exact (by intro entry member; cases member)
theorem rowPhase717 : ∀ entry ∈ rowCases717, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases718 : List PhysicalCase := []
theorem rowFits718 : ∀ entry ∈ rowCases718, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked718 : ∀ entry ∈ rowCases718, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero718 : ∀ entry ∈ rowCases718, entry.hero = 396 := by exact (by intro entry member; cases member)
theorem rowDirection718 : ∀ entry ∈ rowCases718, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase718 : ∀ entry ∈ rowCases718, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases719 : List PhysicalCase := []
theorem rowFits719 : ∀ entry ∈ rowCases719, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked719 : ∀ entry ∈ rowCases719, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero719 : ∀ entry ∈ rowCases719, entry.hero = 396 := by exact (by intro entry member; cases member)
theorem rowDirection719 : ∀ entry ∈ rowCases719, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase719 : ∀ entry ∈ rowCases719, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases720 : List PhysicalCase := [case652, case844]
theorem memberCase652 : case652 ∈ rowCases720 := by exact List.mem_cons_self
theorem memberCase844 : case844 ∈ rowCases720 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits720 : ∀ entry ∈ rowCases720, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case652_fitted, (List.forall_mem_cons.mpr ⟨case844_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked720 : ∀ entry ∈ rowCases720, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame652_checked, (List.forall_mem_cons.mpr ⟨frame844_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero720 : ∀ entry ∈ rowCases720, entry.hero = 397 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection720 : ∀ entry ∈ rowCases720, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase720 : ∀ entry ∈ rowCases720, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases721 : List PhysicalCase := []
theorem rowFits721 : ∀ entry ∈ rowCases721, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked721 : ∀ entry ∈ rowCases721, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero721 : ∀ entry ∈ rowCases721, entry.hero = 397 := by exact (by intro entry member; cases member)
theorem rowDirection721 : ∀ entry ∈ rowCases721, entry.direction = .south := by exact (by intro entry member; cases member)
theorem rowPhase721 : ∀ entry ∈ rowCases721, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases722 : List PhysicalCase := []
theorem rowFits722 : ∀ entry ∈ rowCases722, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked722 : ∀ entry ∈ rowCases722, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero722 : ∀ entry ∈ rowCases722, entry.hero = 397 := by exact (by intro entry member; cases member)
theorem rowDirection722 : ∀ entry ∈ rowCases722, entry.direction = .east := by exact (by intro entry member; cases member)
theorem rowPhase722 : ∀ entry ∈ rowCases722, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases723 : List PhysicalCase := [case653]
theorem memberCase653 : case653 ∈ rowCases723 := by exact List.mem_cons_self
theorem rowFits723 : ∀ entry ∈ rowCases723, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case653_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked723 : ∀ entry ∈ rowCases723, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame653_checked, (by intro entry member; cases member)⟩)
theorem rowHero723 : ∀ entry ∈ rowCases723, entry.hero = 397 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection723 : ∀ entry ∈ rowCases723, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase723 : ∀ entry ∈ rowCases723, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases724 : List PhysicalCase := [case654]
theorem memberCase654 : case654 ∈ rowCases724 := by exact List.mem_cons_self
theorem rowFits724 : ∀ entry ∈ rowCases724, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case654_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked724 : ∀ entry ∈ rowCases724, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame654_checked, (by intro entry member; cases member)⟩)
theorem rowHero724 : ∀ entry ∈ rowCases724, entry.hero = 397 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection724 : ∀ entry ∈ rowCases724, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase724 : ∀ entry ∈ rowCases724, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases725 : List PhysicalCase := [case655]
theorem memberCase655 : case655 ∈ rowCases725 := by exact List.mem_cons_self
theorem rowFits725 : ∀ entry ∈ rowCases725, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case655_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked725 : ∀ entry ∈ rowCases725, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame655_checked, (by intro entry member; cases member)⟩)
theorem rowHero725 : ∀ entry ∈ rowCases725, entry.hero = 397 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection725 : ∀ entry ∈ rowCases725, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase725 : ∀ entry ∈ rowCases725, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases726 : List PhysicalCase := []
theorem rowFits726 : ∀ entry ∈ rowCases726, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked726 : ∀ entry ∈ rowCases726, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero726 : ∀ entry ∈ rowCases726, entry.hero = 397 := by exact (by intro entry member; cases member)
theorem rowDirection726 : ∀ entry ∈ rowCases726, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase726 : ∀ entry ∈ rowCases726, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases727 : List PhysicalCase := []
theorem rowFits727 : ∀ entry ∈ rowCases727, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked727 : ∀ entry ∈ rowCases727, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero727 : ∀ entry ∈ rowCases727, entry.hero = 397 := by exact (by intro entry member; cases member)
theorem rowDirection727 : ∀ entry ∈ rowCases727, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase727 : ∀ entry ∈ rowCases727, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases728 : List PhysicalCase := [case656]
theorem memberCase656 : case656 ∈ rowCases728 := by exact List.mem_cons_self
theorem rowFits728 : ∀ entry ∈ rowCases728, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case656_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked728 : ∀ entry ∈ rowCases728, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame656_checked, (by intro entry member; cases member)⟩)
theorem rowHero728 : ∀ entry ∈ rowCases728, entry.hero = 399 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection728 : ∀ entry ∈ rowCases728, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase728 : ∀ entry ∈ rowCases728, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases729 : List PhysicalCase := []
theorem rowFits729 : ∀ entry ∈ rowCases729, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked729 : ∀ entry ∈ rowCases729, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero729 : ∀ entry ∈ rowCases729, entry.hero = 399 := by exact (by intro entry member; cases member)
theorem rowDirection729 : ∀ entry ∈ rowCases729, entry.direction = .south := by exact (by intro entry member; cases member)
theorem rowPhase729 : ∀ entry ∈ rowCases729, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases730 : List PhysicalCase := [case657]
theorem memberCase657 : case657 ∈ rowCases730 := by exact List.mem_cons_self
theorem rowFits730 : ∀ entry ∈ rowCases730, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case657_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked730 : ∀ entry ∈ rowCases730, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame657_checked, (by intro entry member; cases member)⟩)
theorem rowHero730 : ∀ entry ∈ rowCases730, entry.hero = 399 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection730 : ∀ entry ∈ rowCases730, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase730 : ∀ entry ∈ rowCases730, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases731 : List PhysicalCase := []
theorem rowFits731 : ∀ entry ∈ rowCases731, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked731 : ∀ entry ∈ rowCases731, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero731 : ∀ entry ∈ rowCases731, entry.hero = 399 := by exact (by intro entry member; cases member)
theorem rowDirection731 : ∀ entry ∈ rowCases731, entry.direction = .west := by exact (by intro entry member; cases member)
theorem rowPhase731 : ∀ entry ∈ rowCases731, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases732 : List PhysicalCase := [case658, case659]
theorem memberCase658 : case658 ∈ rowCases732 := by exact List.mem_cons_self
theorem memberCase659 : case659 ∈ rowCases732 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits732 : ∀ entry ∈ rowCases732, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case658_fitted, (List.forall_mem_cons.mpr ⟨case659_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked732 : ∀ entry ∈ rowCases732, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame658_checked, (List.forall_mem_cons.mpr ⟨frame659_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero732 : ∀ entry ∈ rowCases732, entry.hero = 399 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection732 : ∀ entry ∈ rowCases732, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase732 : ∀ entry ∈ rowCases732, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases733 : List PhysicalCase := [case660]
theorem memberCase660 : case660 ∈ rowCases733 := by exact List.mem_cons_self
theorem rowFits733 : ∀ entry ∈ rowCases733, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case660_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked733 : ∀ entry ∈ rowCases733, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame660_checked, (by intro entry member; cases member)⟩)
theorem rowHero733 : ∀ entry ∈ rowCases733, entry.hero = 399 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection733 : ∀ entry ∈ rowCases733, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase733 : ∀ entry ∈ rowCases733, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases734 : List PhysicalCase := []
theorem rowFits734 : ∀ entry ∈ rowCases734, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked734 : ∀ entry ∈ rowCases734, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero734 : ∀ entry ∈ rowCases734, entry.hero = 399 := by exact (by intro entry member; cases member)
theorem rowDirection734 : ∀ entry ∈ rowCases734, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase734 : ∀ entry ∈ rowCases734, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases735 : List PhysicalCase := []
theorem rowFits735 : ∀ entry ∈ rowCases735, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked735 : ∀ entry ∈ rowCases735, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero735 : ∀ entry ∈ rowCases735, entry.hero = 399 := by exact (by intro entry member; cases member)
theorem rowDirection735 : ∀ entry ∈ rowCases735, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase735 : ∀ entry ∈ rowCases735, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases736 : List PhysicalCase := [case661, case852]
theorem memberCase661 : case661 ∈ rowCases736 := by exact List.mem_cons_self
theorem memberCase852 : case852 ∈ rowCases736 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits736 : ∀ entry ∈ rowCases736, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case661_fitted, (List.forall_mem_cons.mpr ⟨case852_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked736 : ∀ entry ∈ rowCases736, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame661_checked, (List.forall_mem_cons.mpr ⟨frame852_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero736 : ∀ entry ∈ rowCases736, entry.hero = 400 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection736 : ∀ entry ∈ rowCases736, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase736 : ∀ entry ∈ rowCases736, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases737 : List PhysicalCase := []
theorem rowFits737 : ∀ entry ∈ rowCases737, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked737 : ∀ entry ∈ rowCases737, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero737 : ∀ entry ∈ rowCases737, entry.hero = 400 := by exact (by intro entry member; cases member)
theorem rowDirection737 : ∀ entry ∈ rowCases737, entry.direction = .south := by exact (by intro entry member; cases member)
theorem rowPhase737 : ∀ entry ∈ rowCases737, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases738 : List PhysicalCase := []
theorem rowFits738 : ∀ entry ∈ rowCases738, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked738 : ∀ entry ∈ rowCases738, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero738 : ∀ entry ∈ rowCases738, entry.hero = 400 := by exact (by intro entry member; cases member)
theorem rowDirection738 : ∀ entry ∈ rowCases738, entry.direction = .east := by exact (by intro entry member; cases member)
theorem rowPhase738 : ∀ entry ∈ rowCases738, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases739 : List PhysicalCase := [case662]
theorem memberCase662 : case662 ∈ rowCases739 := by exact List.mem_cons_self
theorem rowFits739 : ∀ entry ∈ rowCases739, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case662_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked739 : ∀ entry ∈ rowCases739, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame662_checked, (by intro entry member; cases member)⟩)
theorem rowHero739 : ∀ entry ∈ rowCases739, entry.hero = 400 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection739 : ∀ entry ∈ rowCases739, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase739 : ∀ entry ∈ rowCases739, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases740 : List PhysicalCase := []
theorem rowFits740 : ∀ entry ∈ rowCases740, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked740 : ∀ entry ∈ rowCases740, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero740 : ∀ entry ∈ rowCases740, entry.hero = 400 := by exact (by intro entry member; cases member)
theorem rowDirection740 : ∀ entry ∈ rowCases740, entry.direction = .northEast := by exact (by intro entry member; cases member)
theorem rowPhase740 : ∀ entry ∈ rowCases740, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases741 : List PhysicalCase := [case663]
theorem memberCase663 : case663 ∈ rowCases741 := by exact List.mem_cons_self
theorem rowFits741 : ∀ entry ∈ rowCases741, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case663_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked741 : ∀ entry ∈ rowCases741, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame663_checked, (by intro entry member; cases member)⟩)
theorem rowHero741 : ∀ entry ∈ rowCases741, entry.hero = 400 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection741 : ∀ entry ∈ rowCases741, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase741 : ∀ entry ∈ rowCases741, entry.phase = 0 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases742 : List PhysicalCase := []
theorem rowFits742 : ∀ entry ∈ rowCases742, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked742 : ∀ entry ∈ rowCases742, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero742 : ∀ entry ∈ rowCases742, entry.hero = 400 := by exact (by intro entry member; cases member)
theorem rowDirection742 : ∀ entry ∈ rowCases742, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase742 : ∀ entry ∈ rowCases742, entry.phase = 0 := by exact (by intro entry member; cases member)
noncomputable def rowCases743 : List PhysicalCase := []
theorem rowFits743 : ∀ entry ∈ rowCases743, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked743 : ∀ entry ∈ rowCases743, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero743 : ∀ entry ∈ rowCases743, entry.hero = 400 := by exact (by intro entry member; cases member)
theorem rowDirection743 : ∀ entry ∈ rowCases743, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase743 : ∀ entry ∈ rowCases743, entry.phase = 0 := by exact (by intro entry member; cases member)
end NetHack.Soko12Forward220.Unified.P00
