import NetHack.Soko22Hazard87.OracleSound003
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem oracleSound320 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 104 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 104 p) :
    NetHack.Sokoban22Refined85.bonus 104 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 104 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover320 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 82), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local293 p guard decreasing
theorem oracleSound321 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 104 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 104 p) :
    NetHack.Sokoban22Refined85.bonus 104 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 104 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover321 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 126), d1), ((.push 126 (.stay 148)), d0)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local294 p guard decreasing
  · subst entry
    exact local295 p guard decreasing
theorem oracleSound322 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 104 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 104 p) :
    NetHack.Sokoban22Refined85.bonus 104 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 104 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover322 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 105), d1), ((.push 105 (.stay 106)), d0)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local296 p guard decreasing
  · subst entry
    exact local297 p guard decreasing
theorem oracleSound323 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 104 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 104 p) :
    NetHack.Sokoban22Refined85.bonus 104 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 104 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover323 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 103), d1), ((.push 103 (.stay 102)), d0)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local298 p guard decreasing
  · subst entry
    exact local299 p guard decreasing
theorem oracleSound324 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 104 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 104 p) :
    NetHack.Sokoban22Refined85.bonus 104 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 104 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover324 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 83), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local300 p guard decreasing
theorem oracleSound325 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 104 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 104 p) :
    NetHack.Sokoban22Refined85.bonus 104 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 104 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover325 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 81), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local301 p guard decreasing
theorem oracleSound326 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 104 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 104 p) :
    NetHack.Sokoban22Refined85.bonus 104 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 104 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover326 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 127), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local302 p guard decreasing
theorem oracleSound327 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 104 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 104 p) :
    NetHack.Sokoban22Refined85.bonus 104 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 104 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover327 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 125), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local303 p guard decreasing
theorem oracleSound328 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 105 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 105 p) :
    NetHack.Sokoban22Refined85.bonus 105 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 105 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover328 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 83), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local304 p guard decreasing
theorem oracleSound329 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 105 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 105 p) :
    NetHack.Sokoban22Refined85.bonus 105 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 105 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover329 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 127), d1), ((.push 127 (.stay 149)), d0)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local305 p guard decreasing
  · subst entry
    exact local306 p guard decreasing
theorem oracleSound330 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 105 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 105 p) :
    NetHack.Sokoban22Refined85.bonus 105 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 105 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover330 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 106), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local307 p guard decreasing
theorem oracleSound331 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 105 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 105 p) :
    NetHack.Sokoban22Refined85.bonus 105 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 105 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover331 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 104), d1), ((.push 104 (.stay 103)), d0)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local308 p guard decreasing
  · subst entry
    exact local309 p guard decreasing
theorem oracleSound332 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 105 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 105 p) :
    NetHack.Sokoban22Refined85.bonus 105 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 105 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover332 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 84), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local310 p guard decreasing
theorem oracleSound333 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 105 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 105 p) :
    NetHack.Sokoban22Refined85.bonus 105 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 105 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover333 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 82), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local311 p guard decreasing
theorem oracleSound334 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 105 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 105 p) :
    NetHack.Sokoban22Refined85.bonus 105 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 105 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover334 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 128), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local312 p guard decreasing
theorem oracleSound335 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 105 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 105 p) :
    NetHack.Sokoban22Refined85.bonus 105 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 105 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover335 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 126), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local313 p guard decreasing
theorem oracleSound336 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 106 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 106 p) :
    NetHack.Sokoban22Refined85.bonus 106 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 106 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover336 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 84), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local314 p guard decreasing
theorem oracleSound337 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 106 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 106 p) :
    NetHack.Sokoban22Refined85.bonus 106 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 106 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover337 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 128), d1), ((.push 128 (.stay 150)), d0)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local315 p guard decreasing
  · subst entry
    exact local316 p guard decreasing
theorem oracleSound338 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 106 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 106 p) :
    NetHack.Sokoban22Refined85.bonus 106 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 106 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover338 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound339 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 106 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 106 p) :
    NetHack.Sokoban22Refined85.bonus 106 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 106 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover339 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 105), d1), ((.push 105 (.stay 104)), d0)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local317 p guard decreasing
  · subst entry
    exact local318 p guard decreasing
theorem oracleSound340 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 106 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 106 p) :
    NetHack.Sokoban22Refined85.bonus 106 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 106 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover340 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound341 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 106 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 106 p) :
    NetHack.Sokoban22Refined85.bonus 106 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 106 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover341 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 83), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local319 p guard decreasing
theorem oracleSound342 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 106 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 106 p) :
    NetHack.Sokoban22Refined85.bonus 106 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 106 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover342 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound343 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 106 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 106 p) :
    NetHack.Sokoban22Refined85.bonus 106 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 106 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover343 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 127), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local320 p guard decreasing
theorem oracleSound344 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 111 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 111 p) :
    NetHack.Sokoban22Refined85.bonus 111 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 111 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover344 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 89), d74075), ((.push 89 (.stay 67)), d67924)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local321 p guard decreasing
  · subst entry
    exact local322 p guard decreasing
theorem oracleSound345 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 111 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 111 p) :
    NetHack.Sokoban22Refined85.bonus 111 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 111 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover345 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 133), d82685), ((.push 133 (.stay 155)), d82690)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local323 p guard decreasing
  · subst entry
    exact local324 p guard decreasing
theorem oracleSound346 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 111 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 111 p) :
    NetHack.Sokoban22Refined85.bonus 111 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 111 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover346 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound347 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 111 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 111 p) :
    NetHack.Sokoban22Refined85.bonus 111 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 111 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover347 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound348 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 111 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 111 p) :
    NetHack.Sokoban22Refined85.bonus 111 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 111 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover348 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 90), d77113)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local325 p guard decreasing
theorem oracleSound349 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 111 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 111 p) :
    NetHack.Sokoban22Refined85.bonus 111 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 111 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover349 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound350 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 111 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 111 p) :
    NetHack.Sokoban22Refined85.bonus 111 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 111 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover350 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 134), d82694)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local326 p guard decreasing
theorem oracleSound351 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 111 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 111 p) :
    NetHack.Sokoban22Refined85.bonus 111 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 111 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover351 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound352 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 113 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 113 p) :
    NetHack.Sokoban22Refined85.bonus 113 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 113 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover352 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 91), d75629), ((.push 91 (.stay 69)), d70148)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local327 p guard decreasing
  · subst entry
    exact local328 p guard decreasing
theorem oracleSound353 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 113 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 113 p) :
    NetHack.Sokoban22Refined85.bonus 113 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 113 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover353 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 135), d83662), ((.push 135 (.stay 157)), d85724)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local329 p guard decreasing
  · subst entry
    exact local330 p guard decreasing
theorem oracleSound354 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 113 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 113 p) :
    NetHack.Sokoban22Refined85.bonus 113 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 113 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover354 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 114), d89600), ((.push 114 (.stay 115)), d89603)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local331 p guard decreasing
  · subst entry
    exact local332 p guard decreasing
theorem oracleSound355 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 113 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 113 p) :
    NetHack.Sokoban22Refined85.bonus 113 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 113 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover355 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound356 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 113 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 113 p) :
    NetHack.Sokoban22Refined85.bonus 113 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 113 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover356 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound357 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 113 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 113 p) :
    NetHack.Sokoban22Refined85.bonus 113 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 113 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover357 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 90), d75630)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local333 p guard decreasing
theorem oracleSound358 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 113 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 113 p) :
    NetHack.Sokoban22Refined85.bonus 113 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 113 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover358 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 136), d92317)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local334 p guard decreasing
theorem oracleSound359 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 113 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 113 p) :
    NetHack.Sokoban22Refined85.bonus 113 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 113 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover359 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 134), d94517)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local335 p guard decreasing
theorem oracleSound360 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 114 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 114 p) :
    NetHack.Sokoban22Refined85.bonus 114 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 114 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover360 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound361 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 114 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 114 p) :
    NetHack.Sokoban22Refined85.bonus 114 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 114 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover361 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 136), d94518), ((.push 136 (.stay 158)), d94756)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local336 p guard decreasing
  · subst entry
    exact local337 p guard decreasing
theorem oracleSound362 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 114 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 114 p) :
    NetHack.Sokoban22Refined85.bonus 114 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 114 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover362 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 115), d98788), ((.push 115 (.stay 116)), d98791)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local338 p guard decreasing
  · subst entry
    exact local339 p guard decreasing
theorem oracleSound363 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 114 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 114 p) :
    NetHack.Sokoban22Refined85.bonus 114 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 114 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover363 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 113), d89600)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local340 p guard decreasing
theorem oracleSound364 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 114 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 114 p) :
    NetHack.Sokoban22Refined85.bonus 114 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 114 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover364 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 93), d82334)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local341 p guard decreasing
theorem oracleSound365 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 114 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 114 p) :
    NetHack.Sokoban22Refined85.bonus 114 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 114 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover365 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 91), d81525)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local342 p guard decreasing
theorem oracleSound366 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 114 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 114 p) :
    NetHack.Sokoban22Refined85.bonus 114 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 114 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover366 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound367 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 114 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 114 p) :
    NetHack.Sokoban22Refined85.bonus 114 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 114 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover367 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 135), d98801)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local343 p guard decreasing
theorem oracleSound368 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 115 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 115 p) :
    NetHack.Sokoban22Refined85.bonus 115 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 115 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover368 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 93), d82320), ((.push 93 (.stay 71)), d73777)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local344 p guard decreasing
  · subst entry
    exact local345 p guard decreasing
theorem oracleSound369 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 115 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 115 p) :
    NetHack.Sokoban22Refined85.bonus 115 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 115 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover369 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound370 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 115 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 115 p) :
    NetHack.Sokoban22Refined85.bonus 115 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 115 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover370 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 116), d82331)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local346 p guard decreasing
theorem oracleSound371 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 115 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 115 p) :
    NetHack.Sokoban22Refined85.bonus 115 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 115 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover371 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 114), d98788), ((.push 114 (.stay 113)), d89603)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local347 p guard decreasing
  · subst entry
    exact local348 p guard decreasing
theorem oracleSound372 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 115 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 115 p) :
    NetHack.Sokoban22Refined85.bonus 115 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 115 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover372 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 94), d82355)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local349 p guard decreasing
theorem oracleSound373 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 115 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 115 p) :
    NetHack.Sokoban22Refined85.bonus 115 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 115 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover373 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound374 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 115 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 115 p) :
    NetHack.Sokoban22Refined85.bonus 115 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 115 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover374 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 138), d100900)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local350 p guard decreasing
theorem oracleSound375 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 115 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 115 p) :
    NetHack.Sokoban22Refined85.bonus 115 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 115 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover375 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 136), d100902)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local351 p guard decreasing
theorem oracleSound376 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 116 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 116 p) :
    NetHack.Sokoban22Refined85.bonus 116 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 116 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover376 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 94), d82335)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local352 p guard decreasing
theorem oracleSound377 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 116 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 116 p) :
    NetHack.Sokoban22Refined85.bonus 116 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 116 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover377 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 138), d100899), ((.push 138 (.stay 160)), d100907)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local353 p guard decreasing
  · subst entry
    exact local354 p guard decreasing
theorem oracleSound378 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 116 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 116 p) :
    NetHack.Sokoban22Refined85.bonus 116 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 116 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover378 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound379 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 116 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 116 p) :
    NetHack.Sokoban22Refined85.bonus 116 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 116 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover379 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 115), d82331), ((.push 115 (.stay 114)), d98791)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local355 p guard decreasing
  · subst entry
    exact local356 p guard decreasing
theorem oracleSound380 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 116 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 116 p) :
    NetHack.Sokoban22Refined85.bonus 116 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 116 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover380 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 95), d82362)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local357 p guard decreasing
theorem oracleSound381 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 116 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 116 p) :
    NetHack.Sokoban22Refined85.bonus 116 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 116 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover381 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 93), d82333)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local358 p guard decreasing
theorem oracleSound382 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 116 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 116 p) :
    NetHack.Sokoban22Refined85.bonus 116 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 116 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover382 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound383 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 116 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 116 p) :
    NetHack.Sokoban22Refined85.bonus 116 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 116 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover383 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound384 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 118 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 118 p) :
    NetHack.Sokoban22Refined85.bonus 118 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 118 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover384 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 96), d82363), ((.push 96 (.stay 74)), d74052)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local359 p guard decreasing
  · subst entry
    exact local360 p guard decreasing
theorem oracleSound385 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 118 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 118 p) :
    NetHack.Sokoban22Refined85.bonus 118 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 118 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover385 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound386 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 118 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 118 p) :
    NetHack.Sokoban22Refined85.bonus 118 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 118 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover386 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 119), d100937), ((.push 119 (.stay 120)), d100940)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local361 p guard decreasing
  · subst entry
    exact local362 p guard decreasing
theorem oracleSound387 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 118 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 118 p) :
    NetHack.Sokoban22Refined85.bonus 118 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 118 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover387 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound388 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 118 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 118 p) :
    NetHack.Sokoban22Refined85.bonus 118 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 118 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover388 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 97), d82414)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local363 p guard decreasing
theorem oracleSound389 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 118 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 118 p) :
    NetHack.Sokoban22Refined85.bonus 118 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 118 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover389 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 95), d82360)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local364 p guard decreasing
theorem oracleSound390 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 118 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 118 p) :
    NetHack.Sokoban22Refined85.bonus 118 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 118 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover390 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 141), d100942)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local365 p guard decreasing
theorem oracleSound391 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 118 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 118 p) :
    NetHack.Sokoban22Refined85.bonus 118 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 118 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover391 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound392 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 119 p) :
    NetHack.Sokoban22Refined85.bonus 119 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 119 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover392 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 97), d82376)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local366 p guard decreasing
theorem oracleSound393 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 119 p) :
    NetHack.Sokoban22Refined85.bonus 119 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 119 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover393 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 141), d100941), ((.push 141 (.stay 163)), d102055)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local367 p guard decreasing
  · subst entry
    exact local368 p guard decreasing
theorem oracleSound394 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 119 p) :
    NetHack.Sokoban22Refined85.bonus 119 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 119 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover394 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 120), d82407)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local369 p guard decreasing
theorem oracleSound395 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 119 p) :
    NetHack.Sokoban22Refined85.bonus 119 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 119 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover395 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 118), d100937)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local370 p guard decreasing
theorem oracleSound396 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 119 p) :
    NetHack.Sokoban22Refined85.bonus 119 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 119 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover396 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 98), d82422)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local371 p guard decreasing
theorem oracleSound397 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 119 p) :
    NetHack.Sokoban22Refined85.bonus 119 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 119 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover397 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 96), d82375)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local372 p guard decreasing
theorem oracleSound398 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 119 p) :
    NetHack.Sokoban22Refined85.bonus 119 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 119 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover398 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound399 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 119 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 119 p) :
    NetHack.Sokoban22Refined85.bonus 119 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 119 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover399 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
end NetHack.Soko22Hazard87
