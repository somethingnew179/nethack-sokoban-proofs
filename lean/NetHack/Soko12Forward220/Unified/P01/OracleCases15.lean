import NetHack.Soko12Forward220.Unified.P01.OracleCases14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P01
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
noncomputable def rowCases750 : List PhysicalCase := []
theorem rowFits750 : ∀ entry ∈ rowCases750, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked750 : ∀ entry ∈ rowCases750, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero750 : ∀ entry ∈ rowCases750, entry.hero = 400 := by exact (by intro entry member; cases member)
theorem rowDirection750 : ∀ entry ∈ rowCases750, entry.direction = .southEast := by exact (by intro entry member; cases member)
theorem rowPhase750 : ∀ entry ∈ rowCases750, entry.phase = 1 := by exact (by intro entry member; cases member)
noncomputable def rowCases751 : List PhysicalCase := []
theorem rowFits751 : ∀ entry ∈ rowCases751, fits entry = true := by exact (by intro entry member; cases member)
theorem rowChecked751 : ∀ entry ∈ rowCases751, CountedLocalCaseData.check data entry.frame = true := by exact (by intro entry member; cases member)
theorem rowHero751 : ∀ entry ∈ rowCases751, entry.hero = 400 := by exact (by intro entry member; cases member)
theorem rowDirection751 : ∀ entry ∈ rowCases751, entry.direction = .southWest := by exact (by intro entry member; cases member)
theorem rowPhase751 : ∀ entry ∈ rowCases751, entry.phase = 1 := by exact (by intro entry member; cases member)
end NetHack.Soko12Forward220.Unified.P01
