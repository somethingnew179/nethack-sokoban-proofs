import NetHack.Soko12Forward220.Unified.P01.OracleCorners07
import NetHack.Soko12Forward220.Unified.P01.Cases000
import NetHack.Soko12Forward220.Unified.P01.Cases001
import NetHack.Soko12Forward220.Unified.P01.Cases002
import NetHack.Soko12Forward220.Unified.P01.Cases003
import NetHack.Soko12Forward220.Unified.P01.Cases004
import NetHack.Soko12Forward220.Unified.P01.Cases005
import NetHack.Soko12Forward220.Unified.P01.Cases006
import NetHack.Soko12Forward220.Unified.P01.Cases007
import NetHack.Soko12Forward220.Unified.P01.Cases008
import NetHack.Soko12Forward220.Unified.P01.Cases009
import NetHack.Soko12Forward220.Unified.P01.Cases010
import NetHack.Soko12Forward220.Unified.P01.Cases011
import NetHack.Soko12Forward220.Unified.P01.Cases012
import NetHack.Soko12Forward220.Unified.P01.Cases013
import NetHack.Soko12Forward220.Unified.P01.Cases014
import NetHack.Soko12Forward220.Unified.P01.Cases015
import NetHack.Soko12Forward220.Unified.P01.Cases016
import NetHack.Soko12Forward220.Unified.P01.Cases017
import NetHack.Soko12Forward220.Unified.P01.Cases018
import NetHack.Soko12Forward220.Unified.P01.Cases019
import NetHack.Soko12Forward220.Unified.P01.Cases020
import NetHack.Soko12Forward220.Unified.P01.Cases021
import NetHack.Soko12Forward220.Unified.P01.Cases022
import NetHack.Soko12Forward220.Unified.P01.Cases023
import NetHack.Soko12Forward220.Unified.P01.Cases024
import NetHack.Soko12Forward220.Unified.P01.Cases025
import NetHack.Soko12Forward220.Unified.P01.Cases026
import NetHack.Soko12Forward220.Unified.P01.Cases027
import NetHack.Soko12Forward220.Unified.P01.Cases028
import NetHack.Soko12Forward220.Unified.P01.Cases029
import NetHack.Soko12Forward220.Unified.P01.Cases030
import NetHack.Soko12Forward220.Unified.P01.Cases031
import NetHack.Soko12Forward220.Unified.P01.Cases032
import NetHack.Soko12Forward220.Unified.P01.Cases033
import NetHack.Soko12Forward220.Unified.P01.Cases034
import NetHack.Soko12Forward220.Unified.P01.Cases035
import NetHack.Soko12Forward220.Unified.P01.Cases036
import NetHack.Soko12Forward220.Unified.P01.Cases037
import NetHack.Soko12Forward220.Unified.P01.Cases038
import NetHack.Soko12Forward220.Unified.P01.Cases039
import NetHack.Soko12Forward220.Unified.P01.Cases040
import NetHack.Soko12Forward220.Unified.P01.Cases041
import NetHack.Soko12Forward220.Unified.P01.Cases042
import NetHack.Soko12Forward220.Unified.P01.Cases043
import NetHack.Soko12Forward220.Unified.P01.Cases044
import NetHack.Soko12Forward220.Unified.P01.Cases045
import NetHack.Soko12Forward220.Unified.P01.Cases046
import NetHack.Soko12Forward220.Unified.P01.Cases047
import NetHack.Soko12Forward220.Unified.P01.Cases048
import NetHack.Soko12Forward220.Unified.P01.Cases049
import NetHack.Soko12Forward220.Unified.P01.Cases050
import NetHack.Soko12Forward220.Unified.P01.Cases051
import NetHack.Soko12Forward220.Unified.P01.Cases052
import NetHack.Soko12Forward220.Unified.P01.Cases053
import NetHack.Soko12Forward220.Unified.P01.Cases054
import NetHack.Soko12Forward220.Unified.P01.Cases055
import NetHack.Soko12Forward220.Unified.P01.Cases056
import NetHack.Soko12Forward220.Unified.P01.Cases057
import NetHack.Soko12Forward220.Unified.P01.Cases058
import NetHack.Soko12Forward220.Unified.P01.Cases059
import NetHack.Soko12Forward220.Unified.P01.Cases060
import NetHack.Soko12Forward220.Unified.P01.Cases061
import NetHack.Soko12Forward220.Unified.P01.Cases062
import NetHack.Soko12Forward220.Unified.P01.Cases063
import NetHack.Soko12Forward220.Unified.P01.Cases064
import NetHack.Soko12Forward220.Unified.P01.Cases065
import NetHack.Soko12Forward220.Unified.P01.Cases066
import NetHack.Soko12Forward220.Unified.P01.Cases067
import NetHack.Soko12Forward220.Unified.P01.Cases068
import NetHack.Soko12Forward220.Unified.P01.Cases069
import NetHack.Soko12Forward220.Unified.P01.Cases070
import NetHack.Soko12Forward220.Unified.P01.Cases071
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P01
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
noncomputable def rowCases0 : List PhysicalCase := []
theorem rowFits0 : ∀ entry ∈ rowCases0, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked0 : ∀ entry ∈ rowCases0, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero0 : ∀ entry ∈ rowCases0, entry.hero = 29 := by exact (by intro entry member; cases member)
theorem rowDirection0 : ∀ entry ∈ rowCases0, entry.direction = .north := by exact (by intro entry member; cases member)
theorem rowPhase0 : ∀ entry ∈ rowCases0, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases1 : List PhysicalCase := [case000]
theorem memberCase000 : case000 ∈ rowCases1 := by exact List.mem_cons_self
theorem rowFits1 : ∀ entry ∈ rowCases1, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case000_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked1 : ∀ entry ∈ rowCases1, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame000_checked, (by intro entry member; cases member)⟩)
theorem rowHero1 : ∀ entry ∈ rowCases1, entry.hero = 29 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection1 : ∀ entry ∈ rowCases1, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase1 : ∀ entry ∈ rowCases1, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases2 : List PhysicalCase := [case001, case666]
theorem memberCase001 : case001 ∈ rowCases2 := by exact List.mem_cons_self
theorem memberCase666 : case666 ∈ rowCases2 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits2 : ∀ entry ∈ rowCases2, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case001_fitted, (List.forall_mem_cons.mpr ⟨case666_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked2 : ∀ entry ∈ rowCases2, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame001_checked, (List.forall_mem_cons.mpr ⟨frame666_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero2 : ∀ entry ∈ rowCases2, entry.hero = 29 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection2 : ∀ entry ∈ rowCases2, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase2 : ∀ entry ∈ rowCases2, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases3 : List PhysicalCase := []
theorem rowFits3 : ∀ entry ∈ rowCases3, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked3 : ∀ entry ∈ rowCases3, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero3 : ∀ entry ∈ rowCases3, entry.hero = 29 := by exact (by intro entry member; cases member)
theorem rowDirection3 : ∀ entry ∈ rowCases3, entry.direction = .west := by exact (by intro entry member; cases member)
theorem rowPhase3 : ∀ entry ∈ rowCases3, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases4 : List PhysicalCase := []
theorem rowFits4 : ∀ entry ∈ rowCases4, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked4 : ∀ entry ∈ rowCases4, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero4 : ∀ entry ∈ rowCases4, entry.hero = 29 := by exact (by intro entry member; cases member)
theorem rowDirection4 : ∀ entry ∈ rowCases4, entry.direction = .northEast := by exact (by intro entry member; cases member)
theorem rowPhase4 : ∀ entry ∈ rowCases4, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases5 : List PhysicalCase := []
theorem rowFits5 : ∀ entry ∈ rowCases5, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked5 : ∀ entry ∈ rowCases5, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero5 : ∀ entry ∈ rowCases5, entry.hero = 29 := by exact (by intro entry member; cases member)
theorem rowDirection5 : ∀ entry ∈ rowCases5, entry.direction = .northWest := by exact (by intro entry member; cases member)
theorem rowPhase5 : ∀ entry ∈ rowCases5, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases6 : List PhysicalCase := [case002]
theorem memberCase002 : case002 ∈ rowCases6 := by exact List.mem_cons_self
theorem rowFits6 : ∀ entry ∈ rowCases6, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case002_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked6 : ∀ entry ∈ rowCases6, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame002_checked, (by intro entry member; cases member)⟩)
theorem rowHero6 : ∀ entry ∈ rowCases6, entry.hero = 29 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection6 : ∀ entry ∈ rowCases6, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase6 : ∀ entry ∈ rowCases6, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases7 : List PhysicalCase := []
theorem rowFits7 : ∀ entry ∈ rowCases7, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked7 : ∀ entry ∈ rowCases7, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero7 : ∀ entry ∈ rowCases7, entry.hero = 29 := by exact (by intro entry member; cases member)
theorem rowDirection7 : ∀ entry ∈ rowCases7, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase7 : ∀ entry ∈ rowCases7, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases8 : List PhysicalCase := []
theorem rowFits8 : ∀ entry ∈ rowCases8, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked8 : ∀ entry ∈ rowCases8, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero8 : ∀ entry ∈ rowCases8, entry.hero = 30 := by exact (by intro entry member; cases member)
theorem rowDirection8 : ∀ entry ∈ rowCases8, entry.direction = .north := by exact (by intro entry member; cases member)
theorem rowPhase8 : ∀ entry ∈ rowCases8, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases9 : List PhysicalCase := [case003, case669]
theorem memberCase003 : case003 ∈ rowCases9 := by exact List.mem_cons_self
theorem memberCase669 : case669 ∈ rowCases9 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits9 : ∀ entry ∈ rowCases9, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case003_fitted, (List.forall_mem_cons.mpr ⟨case669_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked9 : ∀ entry ∈ rowCases9, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame003_checked, (List.forall_mem_cons.mpr ⟨frame669_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero9 : ∀ entry ∈ rowCases9, entry.hero = 30 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection9 : ∀ entry ∈ rowCases9, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase9 : ∀ entry ∈ rowCases9, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases10 : List PhysicalCase := [case004]
theorem memberCase004 : case004 ∈ rowCases10 := by exact List.mem_cons_self
theorem rowFits10 : ∀ entry ∈ rowCases10, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case004_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked10 : ∀ entry ∈ rowCases10, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame004_checked, (by intro entry member; cases member)⟩)
theorem rowHero10 : ∀ entry ∈ rowCases10, entry.hero = 30 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection10 : ∀ entry ∈ rowCases10, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase10 : ∀ entry ∈ rowCases10, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases11 : List PhysicalCase := [case005]
theorem memberCase005 : case005 ∈ rowCases11 := by exact List.mem_cons_self
theorem rowFits11 : ∀ entry ∈ rowCases11, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case005_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked11 : ∀ entry ∈ rowCases11, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame005_checked, (by intro entry member; cases member)⟩)
theorem rowHero11 : ∀ entry ∈ rowCases11, entry.hero = 30 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection11 : ∀ entry ∈ rowCases11, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase11 : ∀ entry ∈ rowCases11, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases12 : List PhysicalCase := []
theorem rowFits12 : ∀ entry ∈ rowCases12, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked12 : ∀ entry ∈ rowCases12, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero12 : ∀ entry ∈ rowCases12, entry.hero = 30 := by exact (by intro entry member; cases member)
theorem rowDirection12 : ∀ entry ∈ rowCases12, entry.direction = .northEast := by exact (by intro entry member; cases member)
theorem rowPhase12 : ∀ entry ∈ rowCases12, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases13 : List PhysicalCase := []
theorem rowFits13 : ∀ entry ∈ rowCases13, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked13 : ∀ entry ∈ rowCases13, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero13 : ∀ entry ∈ rowCases13, entry.hero = 30 := by exact (by intro entry member; cases member)
theorem rowDirection13 : ∀ entry ∈ rowCases13, entry.direction = .northWest := by exact (by intro entry member; cases member)
theorem rowPhase13 : ∀ entry ∈ rowCases13, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases14 : List PhysicalCase := []
theorem rowFits14 : ∀ entry ∈ rowCases14, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked14 : ∀ entry ∈ rowCases14, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero14 : ∀ entry ∈ rowCases14, entry.hero = 30 := by exact (by intro entry member; cases member)
theorem rowDirection14 : ∀ entry ∈ rowCases14, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase14 : ∀ entry ∈ rowCases14, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases15 : List PhysicalCase := [case006, case007]
theorem memberCase006 : case006 ∈ rowCases15 := by exact List.mem_cons_self
theorem memberCase007 : case007 ∈ rowCases15 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits15 : ∀ entry ∈ rowCases15, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case006_fitted, (List.forall_mem_cons.mpr ⟨case007_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked15 : ∀ entry ∈ rowCases15, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame006_checked, (List.forall_mem_cons.mpr ⟨frame007_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero15 : ∀ entry ∈ rowCases15, entry.hero = 30 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection15 : ∀ entry ∈ rowCases15, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase15 : ∀ entry ∈ rowCases15, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases16 : List PhysicalCase := []
theorem rowFits16 : ∀ entry ∈ rowCases16, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked16 : ∀ entry ∈ rowCases16, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero16 : ∀ entry ∈ rowCases16, entry.hero = 31 := by exact (by intro entry member; cases member)
theorem rowDirection16 : ∀ entry ∈ rowCases16, entry.direction = .north := by exact (by intro entry member; cases member)
theorem rowPhase16 : ∀ entry ∈ rowCases16, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases17 : List PhysicalCase := []
theorem rowFits17 : ∀ entry ∈ rowCases17, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked17 : ∀ entry ∈ rowCases17, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero17 : ∀ entry ∈ rowCases17, entry.hero = 31 := by exact (by intro entry member; cases member)
theorem rowDirection17 : ∀ entry ∈ rowCases17, entry.direction = .south := by exact (by intro entry member; cases member)
theorem rowPhase17 : ∀ entry ∈ rowCases17, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases18 : List PhysicalCase := [case008]
theorem memberCase008 : case008 ∈ rowCases18 := by exact List.mem_cons_self
theorem rowFits18 : ∀ entry ∈ rowCases18, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case008_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked18 : ∀ entry ∈ rowCases18, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame008_checked, (by intro entry member; cases member)⟩)
theorem rowHero18 : ∀ entry ∈ rowCases18, entry.hero = 31 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection18 : ∀ entry ∈ rowCases18, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase18 : ∀ entry ∈ rowCases18, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases19 : List PhysicalCase := [case009, case667]
theorem memberCase009 : case009 ∈ rowCases19 := by exact List.mem_cons_self
theorem memberCase667 : case667 ∈ rowCases19 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits19 : ∀ entry ∈ rowCases19, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case009_fitted, (List.forall_mem_cons.mpr ⟨case667_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked19 : ∀ entry ∈ rowCases19, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame009_checked, (List.forall_mem_cons.mpr ⟨frame667_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero19 : ∀ entry ∈ rowCases19, entry.hero = 31 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection19 : ∀ entry ∈ rowCases19, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase19 : ∀ entry ∈ rowCases19, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases20 : List PhysicalCase := []
theorem rowFits20 : ∀ entry ∈ rowCases20, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked20 : ∀ entry ∈ rowCases20, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero20 : ∀ entry ∈ rowCases20, entry.hero = 31 := by exact (by intro entry member; cases member)
theorem rowDirection20 : ∀ entry ∈ rowCases20, entry.direction = .northEast := by exact (by intro entry member; cases member)
theorem rowPhase20 : ∀ entry ∈ rowCases20, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases21 : List PhysicalCase := []
theorem rowFits21 : ∀ entry ∈ rowCases21, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked21 : ∀ entry ∈ rowCases21, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero21 : ∀ entry ∈ rowCases21, entry.hero = 31 := by exact (by intro entry member; cases member)
theorem rowDirection21 : ∀ entry ∈ rowCases21, entry.direction = .northWest := by exact (by intro entry member; cases member)
theorem rowPhase21 : ∀ entry ∈ rowCases21, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases22 : List PhysicalCase := []
theorem rowFits22 : ∀ entry ∈ rowCases22, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked22 : ∀ entry ∈ rowCases22, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero22 : ∀ entry ∈ rowCases22, entry.hero = 31 := by exact (by intro entry member; cases member)
theorem rowDirection22 : ∀ entry ∈ rowCases22, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase22 : ∀ entry ∈ rowCases22, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases23 : List PhysicalCase := [case010]
theorem memberCase010 : case010 ∈ rowCases23 := by exact List.mem_cons_self
theorem rowFits23 : ∀ entry ∈ rowCases23, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case010_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked23 : ∀ entry ∈ rowCases23, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame010_checked, (by intro entry member; cases member)⟩)
theorem rowHero23 : ∀ entry ∈ rowCases23, entry.hero = 31 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection23 : ∀ entry ∈ rowCases23, entry.direction = .southWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase23 : ∀ entry ∈ rowCases23, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases24 : List PhysicalCase := []
theorem rowFits24 : ∀ entry ∈ rowCases24, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked24 : ∀ entry ∈ rowCases24, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero24 : ∀ entry ∈ rowCases24, entry.hero = 32 := by exact (by intro entry member; cases member)
theorem rowDirection24 : ∀ entry ∈ rowCases24, entry.direction = .north := by exact (by intro entry member; cases member)
theorem rowPhase24 : ∀ entry ∈ rowCases24, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases25 : List PhysicalCase := []
theorem rowFits25 : ∀ entry ∈ rowCases25, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked25 : ∀ entry ∈ rowCases25, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero25 : ∀ entry ∈ rowCases25, entry.hero = 32 := by exact (by intro entry member; cases member)
theorem rowDirection25 : ∀ entry ∈ rowCases25, entry.direction = .south := by exact (by intro entry member; cases member)
theorem rowPhase25 : ∀ entry ∈ rowCases25, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases26 : List PhysicalCase := []
theorem rowFits26 : ∀ entry ∈ rowCases26, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked26 : ∀ entry ∈ rowCases26, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero26 : ∀ entry ∈ rowCases26, entry.hero = 32 := by exact (by intro entry member; cases member)
theorem rowDirection26 : ∀ entry ∈ rowCases26, entry.direction = .east := by exact (by intro entry member; cases member)
theorem rowPhase26 : ∀ entry ∈ rowCases26, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases27 : List PhysicalCase := [case011]
theorem memberCase011 : case011 ∈ rowCases27 := by exact List.mem_cons_self
theorem rowFits27 : ∀ entry ∈ rowCases27, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case011_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked27 : ∀ entry ∈ rowCases27, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame011_checked, (by intro entry member; cases member)⟩)
theorem rowHero27 : ∀ entry ∈ rowCases27, entry.hero = 32 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection27 : ∀ entry ∈ rowCases27, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase27 : ∀ entry ∈ rowCases27, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases28 : List PhysicalCase := []
theorem rowFits28 : ∀ entry ∈ rowCases28, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked28 : ∀ entry ∈ rowCases28, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero28 : ∀ entry ∈ rowCases28, entry.hero = 32 := by exact (by intro entry member; cases member)
theorem rowDirection28 : ∀ entry ∈ rowCases28, entry.direction = .northEast := by exact (by intro entry member; cases member)
theorem rowPhase28 : ∀ entry ∈ rowCases28, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases29 : List PhysicalCase := []
theorem rowFits29 : ∀ entry ∈ rowCases29, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked29 : ∀ entry ∈ rowCases29, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero29 : ∀ entry ∈ rowCases29, entry.hero = 32 := by exact (by intro entry member; cases member)
theorem rowDirection29 : ∀ entry ∈ rowCases29, entry.direction = .northWest := by exact (by intro entry member; cases member)
theorem rowPhase29 : ∀ entry ∈ rowCases29, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases30 : List PhysicalCase := []
theorem rowFits30 : ∀ entry ∈ rowCases30, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked30 : ∀ entry ∈ rowCases30, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero30 : ∀ entry ∈ rowCases30, entry.hero = 32 := by exact (by intro entry member; cases member)
theorem rowDirection30 : ∀ entry ∈ rowCases30, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase30 : ∀ entry ∈ rowCases30, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases31 : List PhysicalCase := []
theorem rowFits31 : ∀ entry ∈ rowCases31, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked31 : ∀ entry ∈ rowCases31, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero31 : ∀ entry ∈ rowCases31, entry.hero = 32 := by exact (by intro entry member; cases member)
theorem rowDirection31 : ∀ entry ∈ rowCases31, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase31 : ∀ entry ∈ rowCases31, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases32 : List PhysicalCase := [case012]
theorem memberCase012 : case012 ∈ rowCases32 := by exact List.mem_cons_self
theorem rowFits32 : ∀ entry ∈ rowCases32, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case012_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked32 : ∀ entry ∈ rowCases32, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame012_checked, (by intro entry member; cases member)⟩)
theorem rowHero32 : ∀ entry ∈ rowCases32, entry.hero = 55 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection32 : ∀ entry ∈ rowCases32, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase32 : ∀ entry ∈ rowCases32, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases33 : List PhysicalCase := []
theorem rowFits33 : ∀ entry ∈ rowCases33, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked33 : ∀ entry ∈ rowCases33, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero33 : ∀ entry ∈ rowCases33, entry.hero = 55 := by exact (by intro entry member; cases member)
theorem rowDirection33 : ∀ entry ∈ rowCases33, entry.direction = .south := by exact (by intro entry member; cases member)
theorem rowPhase33 : ∀ entry ∈ rowCases33, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases34 : List PhysicalCase := [case013]
theorem memberCase013 : case013 ∈ rowCases34 := by exact List.mem_cons_self
theorem rowFits34 : ∀ entry ∈ rowCases34, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case013_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked34 : ∀ entry ∈ rowCases34, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame013_checked, (by intro entry member; cases member)⟩)
theorem rowHero34 : ∀ entry ∈ rowCases34, entry.hero = 55 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection34 : ∀ entry ∈ rowCases34, entry.direction = .east := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase34 : ∀ entry ∈ rowCases34, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases35 : List PhysicalCase := []
theorem rowFits35 : ∀ entry ∈ rowCases35, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked35 : ∀ entry ∈ rowCases35, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero35 : ∀ entry ∈ rowCases35, entry.hero = 55 := by exact (by intro entry member; cases member)
theorem rowDirection35 : ∀ entry ∈ rowCases35, entry.direction = .west := by exact (by intro entry member; cases member)
theorem rowPhase35 : ∀ entry ∈ rowCases35, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases36 : List PhysicalCase := [case014, case015]
theorem memberCase014 : case014 ∈ rowCases36 := by exact List.mem_cons_self
theorem memberCase015 : case015 ∈ rowCases36 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits36 : ∀ entry ∈ rowCases36, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case014_fitted, (List.forall_mem_cons.mpr ⟨case015_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked36 : ∀ entry ∈ rowCases36, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame014_checked, (List.forall_mem_cons.mpr ⟨frame015_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero36 : ∀ entry ∈ rowCases36, entry.hero = 55 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection36 : ∀ entry ∈ rowCases36, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase36 : ∀ entry ∈ rowCases36, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases37 : List PhysicalCase := []
theorem rowFits37 : ∀ entry ∈ rowCases37, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked37 : ∀ entry ∈ rowCases37, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero37 : ∀ entry ∈ rowCases37, entry.hero = 55 := by exact (by intro entry member; cases member)
theorem rowDirection37 : ∀ entry ∈ rowCases37, entry.direction = .northWest := by exact (by intro entry member; cases member)
theorem rowPhase37 : ∀ entry ∈ rowCases37, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases38 : List PhysicalCase := [case016]
theorem memberCase016 : case016 ∈ rowCases38 := by exact List.mem_cons_self
theorem rowFits38 : ∀ entry ∈ rowCases38, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case016_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked38 : ∀ entry ∈ rowCases38, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame016_checked, (by intro entry member; cases member)⟩)
theorem rowHero38 : ∀ entry ∈ rowCases38, entry.hero = 55 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection38 : ∀ entry ∈ rowCases38, entry.direction = .southEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase38 : ∀ entry ∈ rowCases38, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases39 : List PhysicalCase := []
theorem rowFits39 : ∀ entry ∈ rowCases39, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked39 : ∀ entry ∈ rowCases39, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero39 : ∀ entry ∈ rowCases39, entry.hero = 55 := by exact (by intro entry member; cases member)
theorem rowDirection39 : ∀ entry ∈ rowCases39, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase39 : ∀ entry ∈ rowCases39, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases40 : List PhysicalCase := [case017]
theorem memberCase017 : case017 ∈ rowCases40 := by exact List.mem_cons_self
theorem rowFits40 : ∀ entry ∈ rowCases40, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case017_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked40 : ∀ entry ∈ rowCases40, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame017_checked, (by intro entry member; cases member)⟩)
theorem rowHero40 : ∀ entry ∈ rowCases40, entry.hero = 56 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection40 : ∀ entry ∈ rowCases40, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase40 : ∀ entry ∈ rowCases40, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases41 : List PhysicalCase := [case018, case671]
theorem memberCase018 : case018 ∈ rowCases41 := by exact List.mem_cons_self
theorem memberCase671 : case671 ∈ rowCases41 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits41 : ∀ entry ∈ rowCases41, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case018_fitted, (List.forall_mem_cons.mpr ⟨case671_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked41 : ∀ entry ∈ rowCases41, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame018_checked, (List.forall_mem_cons.mpr ⟨frame671_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero41 : ∀ entry ∈ rowCases41, entry.hero = 56 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection41 : ∀ entry ∈ rowCases41, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase41 : ∀ entry ∈ rowCases41, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases42 : List PhysicalCase := []
theorem rowFits42 : ∀ entry ∈ rowCases42, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked42 : ∀ entry ∈ rowCases42, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero42 : ∀ entry ∈ rowCases42, entry.hero = 56 := by exact (by intro entry member; cases member)
theorem rowDirection42 : ∀ entry ∈ rowCases42, entry.direction = .east := by exact (by intro entry member; cases member)
theorem rowPhase42 : ∀ entry ∈ rowCases42, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases43 : List PhysicalCase := [case019]
theorem memberCase019 : case019 ∈ rowCases43 := by exact List.mem_cons_self
theorem rowFits43 : ∀ entry ∈ rowCases43, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case019_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked43 : ∀ entry ∈ rowCases43, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame019_checked, (by intro entry member; cases member)⟩)
theorem rowHero43 : ∀ entry ∈ rowCases43, entry.hero = 56 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection43 : ∀ entry ∈ rowCases43, entry.direction = .west := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase43 : ∀ entry ∈ rowCases43, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases44 : List PhysicalCase := [case020]
theorem memberCase020 : case020 ∈ rowCases44 := by exact List.mem_cons_self
theorem rowFits44 : ∀ entry ∈ rowCases44, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case020_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked44 : ∀ entry ∈ rowCases44, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame020_checked, (by intro entry member; cases member)⟩)
theorem rowHero44 : ∀ entry ∈ rowCases44, entry.hero = 56 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection44 : ∀ entry ∈ rowCases44, entry.direction = .northEast := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase44 : ∀ entry ∈ rowCases44, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases45 : List PhysicalCase := [case021]
theorem memberCase021 : case021 ∈ rowCases45 := by exact List.mem_cons_self
theorem rowFits45 : ∀ entry ∈ rowCases45, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case021_fitted, (by intro entry member; cases member)⟩)
theorem rowChecked45 : ∀ entry ∈ rowCases45, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame021_checked, (by intro entry member; cases member)⟩)
theorem rowHero45 : ∀ entry ∈ rowCases45, entry.hero = 56 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowDirection45 : ∀ entry ∈ rowCases45, entry.direction = .northWest := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
theorem rowPhase45 : ∀ entry ∈ rowCases45, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)
noncomputable def rowCases46 : List PhysicalCase := []
theorem rowFits46 : ∀ entry ∈ rowCases46, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked46 : ∀ entry ∈ rowCases46, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero46 : ∀ entry ∈ rowCases46, entry.hero = 56 := by exact (by intro entry member; cases member)
theorem rowDirection46 : ∀ entry ∈ rowCases46, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase46 : ∀ entry ∈ rowCases46, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases47 : List PhysicalCase := []
theorem rowFits47 : ∀ entry ∈ rowCases47, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked47 : ∀ entry ∈ rowCases47, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero47 : ∀ entry ∈ rowCases47, entry.hero = 56 := by exact (by intro entry member; cases member)
theorem rowDirection47 : ∀ entry ∈ rowCases47, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase47 : ∀ entry ∈ rowCases47, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases48 : List PhysicalCase := [case022, case668]
theorem memberCase022 : case022 ∈ rowCases48 := by exact List.mem_cons_self
theorem memberCase668 : case668 ∈ rowCases48 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits48 : ∀ entry ∈ rowCases48, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case022_fitted, (List.forall_mem_cons.mpr ⟨case668_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked48 : ∀ entry ∈ rowCases48, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame022_checked, (List.forall_mem_cons.mpr ⟨frame668_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero48 : ∀ entry ∈ rowCases48, entry.hero = 82 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection48 : ∀ entry ∈ rowCases48, entry.direction = .north := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase48 : ∀ entry ∈ rowCases48, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
noncomputable def rowCases49 : List PhysicalCase := [case023, case673]
theorem memberCase023 : case023 ∈ rowCases49 := by exact List.mem_cons_self
theorem memberCase673 : case673 ∈ rowCases49 := by exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem rowFits49 : ∀ entry ∈ rowCases49, fits entry = true := by exact (List.forall_mem_cons.mpr ⟨case023_fitted, (List.forall_mem_cons.mpr ⟨case673_fitted, (by intro entry member; cases member)⟩)⟩)
theorem rowChecked49 : ∀ entry ∈ rowCases49, CountedLocalCaseData.check data entry.frame = true := by exact (List.forall_mem_cons.mpr ⟨frame023_checked, (List.forall_mem_cons.mpr ⟨frame673_checked, (by intro entry member; cases member)⟩)⟩)
theorem rowHero49 : ∀ entry ∈ rowCases49, entry.hero = 82 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowDirection49 : ∀ entry ∈ rowCases49, entry.direction = .south := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
theorem rowPhase49 : ∀ entry ∈ rowCases49, entry.phase = 1 := by exact (List.forall_mem_cons.mpr ⟨rfl, (List.forall_mem_cons.mpr ⟨rfl, (by intro entry member; cases member)⟩)⟩)
end NetHack.Soko12Forward220.Unified.P01
