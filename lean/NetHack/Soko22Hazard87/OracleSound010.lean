import NetHack.Soko22Hazard87.OracleSound009
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem oracleSound800 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 193 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 193 p) :
    NetHack.Sokoban22Refined85.bonus 193 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 193 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover800 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 171), d1), ((.push 171 (.stay 149)), d0)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local821 p guard decreasing
  · subst entry
    exact local822 p guard decreasing
theorem oracleSound801 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 193 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 193 p) :
    NetHack.Sokoban22Refined85.bonus 193 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 193 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover801 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 215), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local823 p guard decreasing
theorem oracleSound802 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 193 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 193 p) :
    NetHack.Sokoban22Refined85.bonus 193 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 193 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover802 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 194), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local824 p guard decreasing
theorem oracleSound803 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 193 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 193 p) :
    NetHack.Sokoban22Refined85.bonus 193 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 193 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover803 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 192), d1), ((.push 192 (.stay 191)), d0)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local825 p guard decreasing
  · subst entry
    exact local826 p guard decreasing
theorem oracleSound804 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 193 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 193 p) :
    NetHack.Sokoban22Refined85.bonus 193 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 193 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover804 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 172), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local827 p guard decreasing
theorem oracleSound805 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 193 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 193 p) :
    NetHack.Sokoban22Refined85.bonus 193 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 193 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover805 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 170), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local828 p guard decreasing
theorem oracleSound806 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 193 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 193 p) :
    NetHack.Sokoban22Refined85.bonus 193 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 193 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover806 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 216), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local829 p guard decreasing
theorem oracleSound807 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 193 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 193 p) :
    NetHack.Sokoban22Refined85.bonus 193 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 193 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover807 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 214), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local830 p guard decreasing
theorem oracleSound808 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 194 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 194 p) :
    NetHack.Sokoban22Refined85.bonus 194 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 194 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover808 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 172), d1), ((.push 172 (.stay 150)), d0)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local831 p guard decreasing
  · subst entry
    exact local832 p guard decreasing
theorem oracleSound809 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 194 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 194 p) :
    NetHack.Sokoban22Refined85.bonus 194 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 194 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover809 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 216), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local833 p guard decreasing
theorem oracleSound810 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 194 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 194 p) :
    NetHack.Sokoban22Refined85.bonus 194 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 194 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover810 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound811 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 194 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 194 p) :
    NetHack.Sokoban22Refined85.bonus 194 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 194 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover811 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 193), d1), ((.push 193 (.stay 192)), d0)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local834 p guard decreasing
  · subst entry
    exact local835 p guard decreasing
theorem oracleSound812 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 194 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 194 p) :
    NetHack.Sokoban22Refined85.bonus 194 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 194 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover812 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound813 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 194 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 194 p) :
    NetHack.Sokoban22Refined85.bonus 194 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 194 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover813 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 171), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local836 p guard decreasing
theorem oracleSound814 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 194 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 194 p) :
    NetHack.Sokoban22Refined85.bonus 194 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 194 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover814 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound815 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 194 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 194 p) :
    NetHack.Sokoban22Refined85.bonus 194 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 194 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover815 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 215), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local837 p guard decreasing
theorem oracleSound816 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 199 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 199 p) :
    NetHack.Sokoban22Refined85.bonus 199 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 199 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover816 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 177), d194333), ((.push 177 (.stay 155)), d132769)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local838 p guard decreasing
  · subst entry
    exact local839 p guard decreasing
theorem oracleSound817 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 199 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 199 p) :
    NetHack.Sokoban22Refined85.bonus 199 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 199 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover817 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound818 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 199 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 199 p) :
    NetHack.Sokoban22Refined85.bonus 199 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 199 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover818 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 200), d194336), ((.push 200 (.stay 201)), d227687)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local840 p guard decreasing
  · subst entry
    exact local841 p guard decreasing
theorem oracleSound819 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 199 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 199 p) :
    NetHack.Sokoban22Refined85.bonus 199 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 199 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover819 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound820 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 199 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 199 p) :
    NetHack.Sokoban22Refined85.bonus 199 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 199 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover820 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound821 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 199 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 199 p) :
    NetHack.Sokoban22Refined85.bonus 199 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 199 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover821 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound822 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 199 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 199 p) :
    NetHack.Sokoban22Refined85.bonus 199 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 199 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover822 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound823 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 199 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 199 p) :
    NetHack.Sokoban22Refined85.bonus 199 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 199 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover823 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound824 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 200 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 200 p) :
    NetHack.Sokoban22Refined85.bonus 200 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 200 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover824 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound825 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 200 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 200 p) :
    NetHack.Sokoban22Refined85.bonus 200 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 200 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover825 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound826 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 200 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 200 p) :
    NetHack.Sokoban22Refined85.bonus 200 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 200 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover826 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 201), d231166), ((.push 201 (.stay 202)), d231382)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local842 p guard decreasing
  · subst entry
    exact local843 p guard decreasing
theorem oracleSound827 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 200 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 200 p) :
    NetHack.Sokoban22Refined85.bonus 200 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 200 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover827 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 199), d194336)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local844 p guard decreasing
theorem oracleSound828 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 200 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 200 p) :
    NetHack.Sokoban22Refined85.bonus 200 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 200 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover828 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound829 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 200 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 200 p) :
    NetHack.Sokoban22Refined85.bonus 200 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 200 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover829 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 177), d194337)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local845 p guard decreasing
theorem oracleSound830 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 200 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 200 p) :
    NetHack.Sokoban22Refined85.bonus 200 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 200 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover830 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 223), d236583)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local846 p guard decreasing
theorem oracleSound831 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 200 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 200 p) :
    NetHack.Sokoban22Refined85.bonus 200 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 200 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover831 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound832 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 201 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 201 p) :
    NetHack.Sokoban22Refined85.bonus 201 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 201 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover832 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound833 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 201 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 201 p) :
    NetHack.Sokoban22Refined85.bonus 201 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 201 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover833 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 223), d236582), ((.push 223 (.stay 245)), d239127)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local847 p guard decreasing
  · subst entry
    exact local848 p guard decreasing
theorem oracleSound834 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 201 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 201 p) :
    NetHack.Sokoban22Refined85.bonus 201 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 201 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover834 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 202), d208034)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local849 p guard decreasing
theorem oracleSound835 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 201 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 201 p) :
    NetHack.Sokoban22Refined85.bonus 201 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 201 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover835 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 200), d231166), ((.push 200 (.stay 199)), d227687)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local850 p guard decreasing
  · subst entry
    exact local851 p guard decreasing
theorem oracleSound836 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 201 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 201 p) :
    NetHack.Sokoban22Refined85.bonus 201 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 201 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover836 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 180), d208035)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local852 p guard decreasing
theorem oracleSound837 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 201 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 201 p) :
    NetHack.Sokoban22Refined85.bonus 201 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 201 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover837 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound838 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 201 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 201 p) :
    NetHack.Sokoban22Refined85.bonus 201 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 201 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover838 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 224), d241832)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local853 p guard decreasing
theorem oracleSound839 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 201 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 201 p) :
    NetHack.Sokoban22Refined85.bonus 201 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 201 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover839 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound840 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 202 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 202 p) :
    NetHack.Sokoban22Refined85.bonus 202 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 202 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover840 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 180), d198467), ((.push 180 (.stay 158)), d152855)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local854 p guard decreasing
  · subst entry
    exact local855 p guard decreasing
theorem oracleSound841 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 202 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 202 p) :
    NetHack.Sokoban22Refined85.bonus 202 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 202 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover841 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 224), d251389), ((.push 224 (.stay 246)), d253272)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local856 p guard decreasing
  · subst entry
    exact local857 p guard decreasing
theorem oracleSound842 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 202 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 202 p) :
    NetHack.Sokoban22Refined85.bonus 202 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 202 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover842 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound843 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 202 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 202 p) :
    NetHack.Sokoban22Refined85.bonus 202 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 202 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover843 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 201), d208034), ((.push 201 (.stay 200)), d231382)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local858 p guard decreasing
  · subst entry
    exact local859 p guard decreasing
theorem oracleSound844 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 202 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 202 p) :
    NetHack.Sokoban22Refined85.bonus 202 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 202 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover844 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 181), d212559)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local860 p guard decreasing
theorem oracleSound845 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 202 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 202 p) :
    NetHack.Sokoban22Refined85.bonus 202 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 202 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover845 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound846 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 202 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 202 p) :
    NetHack.Sokoban22Refined85.bonus 202 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 202 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover846 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 225), d261986)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local861 p guard decreasing
theorem oracleSound847 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 202 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 202 p) :
    NetHack.Sokoban22Refined85.bonus 202 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 202 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover847 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 223), d266246)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local862 p guard decreasing
theorem oracleSound848 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 204 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 204 p) :
    NetHack.Sokoban22Refined85.bonus 204 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 204 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover848 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 182), d211415), ((.push 182 (.stay 160)), d171300)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local863 p guard decreasing
  · subst entry
    exact local864 p guard decreasing
theorem oracleSound849 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 204 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 204 p) :
    NetHack.Sokoban22Refined85.bonus 204 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 204 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover849 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 226), d267844), ((.push 226 (.stay 248)), d271212)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local865 p guard decreasing
  · subst entry
    exact local866 p guard decreasing
theorem oracleSound850 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 204 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 204 p) :
    NetHack.Sokoban22Refined85.bonus 204 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 204 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover850 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound851 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 204 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 204 p) :
    NetHack.Sokoban22Refined85.bonus 204 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 204 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover851 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound852 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 204 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 204 p) :
    NetHack.Sokoban22Refined85.bonus 204 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 204 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover852 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound853 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 204 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 204 p) :
    NetHack.Sokoban22Refined85.bonus 204 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 204 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover853 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 181), d211416)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local867 p guard decreasing
theorem oracleSound854 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 204 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 204 p) :
    NetHack.Sokoban22Refined85.bonus 204 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 204 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover854 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound855 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 204 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 204 p) :
    NetHack.Sokoban22Refined85.bonus 204 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 204 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover855 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 225), d277740)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local868 p guard decreasing
theorem oracleSound856 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 210 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 210 p) :
    NetHack.Sokoban22Refined85.bonus 210 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 210 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover856 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 188), d1), ((.push 188 (.stay 166)), d0)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local869 p guard decreasing
  · subst entry
    exact local870 p guard decreasing
theorem oracleSound857 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 210 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 210 p) :
    NetHack.Sokoban22Refined85.bonus 210 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 210 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover857 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound858 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 210 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 210 p) :
    NetHack.Sokoban22Refined85.bonus 210 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 210 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover858 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 211), d1), ((.push 211 (.stay 212)), d0)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local871 p guard decreasing
  · subst entry
    exact local872 p guard decreasing
theorem oracleSound859 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 210 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 210 p) :
    NetHack.Sokoban22Refined85.bonus 210 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 210 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover859 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound860 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 210 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 210 p) :
    NetHack.Sokoban22Refined85.bonus 210 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 210 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover860 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 189), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local873 p guard decreasing
theorem oracleSound861 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 210 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 210 p) :
    NetHack.Sokoban22Refined85.bonus 210 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 210 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover861 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound862 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 210 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 210 p) :
    NetHack.Sokoban22Refined85.bonus 210 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 210 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover862 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound863 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 210 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 210 p) :
    NetHack.Sokoban22Refined85.bonus 210 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 210 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover863 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound864 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 211 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 211 p) :
    NetHack.Sokoban22Refined85.bonus 211 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 211 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover864 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 189), d1), ((.push 189 (.stay 167)), d0)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local874 p guard decreasing
  · subst entry
    exact local875 p guard decreasing
theorem oracleSound865 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 211 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 211 p) :
    NetHack.Sokoban22Refined85.bonus 211 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 211 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover865 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound866 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 211 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 211 p) :
    NetHack.Sokoban22Refined85.bonus 211 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 211 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover866 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 212), d1), ((.push 212 (.stay 213)), d0)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local876 p guard decreasing
  · subst entry
    exact local877 p guard decreasing
theorem oracleSound867 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 211 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 211 p) :
    NetHack.Sokoban22Refined85.bonus 211 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 211 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover867 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 210), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local878 p guard decreasing
theorem oracleSound868 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 211 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 211 p) :
    NetHack.Sokoban22Refined85.bonus 211 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 211 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover868 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 190), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local879 p guard decreasing
theorem oracleSound869 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 211 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 211 p) :
    NetHack.Sokoban22Refined85.bonus 211 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 211 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover869 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 188), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local880 p guard decreasing
theorem oracleSound870 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 211 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 211 p) :
    NetHack.Sokoban22Refined85.bonus 211 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 211 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover870 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound871 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 211 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 211 p) :
    NetHack.Sokoban22Refined85.bonus 211 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 211 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover871 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound872 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 212 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 212 p) :
    NetHack.Sokoban22Refined85.bonus 212 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 212 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover872 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 190), d1), ((.push 190 (.stay 168)), d0)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local881 p guard decreasing
  · subst entry
    exact local882 p guard decreasing
theorem oracleSound873 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 212 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 212 p) :
    NetHack.Sokoban22Refined85.bonus 212 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 212 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover873 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound874 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 212 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 212 p) :
    NetHack.Sokoban22Refined85.bonus 212 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 212 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover874 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 213), d1), ((.push 213 (.stay 214)), d0)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local883 p guard decreasing
  · subst entry
    exact local884 p guard decreasing
theorem oracleSound875 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 212 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 212 p) :
    NetHack.Sokoban22Refined85.bonus 212 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 212 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover875 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 211), d1), ((.push 211 (.stay 210)), d0)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local885 p guard decreasing
  · subst entry
    exact local886 p guard decreasing
theorem oracleSound876 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 212 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 212 p) :
    NetHack.Sokoban22Refined85.bonus 212 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 212 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover876 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 191), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local887 p guard decreasing
theorem oracleSound877 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 212 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 212 p) :
    NetHack.Sokoban22Refined85.bonus 212 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 212 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover877 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 189), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local888 p guard decreasing
theorem oracleSound878 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 212 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 212 p) :
    NetHack.Sokoban22Refined85.bonus 212 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 212 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover878 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound879 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 212 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 212 p) :
    NetHack.Sokoban22Refined85.bonus 212 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 212 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover879 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
end NetHack.Soko22Hazard87
