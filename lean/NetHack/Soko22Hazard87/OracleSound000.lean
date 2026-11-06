import NetHack.Soko22Hazard87.Numeric015
import NetHack.Soko22Hazard87.OracleCover031
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem oracleSound0 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 25 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 25 p) :
    NetHack.Sokoban22Refined85.bonus 25 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 25 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover0 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound1 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 25 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 25 p) :
    NetHack.Sokoban22Refined85.bonus 25 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 25 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover1 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 47), d51640), ((.push 47 (.stay 69)), d53870)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local0 p guard decreasing
  · subst entry
    exact local1 p guard decreasing
theorem oracleSound2 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 25 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 25 p) :
    NetHack.Sokoban22Refined85.bonus 25 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 25 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover2 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound3 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 25 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 25 p) :
    NetHack.Sokoban22Refined85.bonus 25 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 25 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover3 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound4 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 25 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 25 p) :
    NetHack.Sokoban22Refined85.bonus 25 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 25 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover4 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound5 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 25 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 25 p) :
    NetHack.Sokoban22Refined85.bonus 25 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 25 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover5 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound6 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 25 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 25 p) :
    NetHack.Sokoban22Refined85.bonus 25 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 25 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover6 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 48), d54186)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local2 p guard decreasing
theorem oracleSound7 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 25 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 25 p) :
    NetHack.Sokoban22Refined85.bonus 25 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 25 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover7 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 46), d54513)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local3 p guard decreasing
theorem oracleSound8 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 27 p) :
    NetHack.Sokoban22Refined85.bonus 27 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 27 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover8 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound9 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 27 p) :
    NetHack.Sokoban22Refined85.bonus 27 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 27 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover9 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 49), d54518), ((.push 49 (.stay 71)), d54981)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local4 p guard decreasing
  · subst entry
    exact local5 p guard decreasing
theorem oracleSound10 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 27 p) :
    NetHack.Sokoban22Refined85.bonus 27 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 27 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover10 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 28), d55597), ((.push 28 (.stay 29)), d55749)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local6 p guard decreasing
  · subst entry
    exact local7 p guard decreasing
theorem oracleSound11 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 27 p) :
    NetHack.Sokoban22Refined85.bonus 27 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 27 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover11 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound12 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 27 p) :
    NetHack.Sokoban22Refined85.bonus 27 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 27 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover12 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound13 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 27 p) :
    NetHack.Sokoban22Refined85.bonus 27 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 27 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover13 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound14 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 27 p) :
    NetHack.Sokoban22Refined85.bonus 27 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 27 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover14 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 50), d55757)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local8 p guard decreasing
theorem oracleSound15 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 27 p) :
    NetHack.Sokoban22Refined85.bonus 27 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 27 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover15 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 48), d55879)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local9 p guard decreasing
theorem oracleSound16 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 28 p) :
    NetHack.Sokoban22Refined85.bonus 28 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 28 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover16 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound17 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 28 p) :
    NetHack.Sokoban22Refined85.bonus 28 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 28 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover17 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 50), d55880)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local10 p guard decreasing
theorem oracleSound18 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 28 p) :
    NetHack.Sokoban22Refined85.bonus 28 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 28 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover18 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 29), d55881), ((.push 29 (.stay 30)), d55886)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local11 p guard decreasing
  · subst entry
    exact local12 p guard decreasing
theorem oracleSound19 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 28 p) :
    NetHack.Sokoban22Refined85.bonus 28 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 28 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover19 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 27), d55597)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local13 p guard decreasing
theorem oracleSound20 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 28 p) :
    NetHack.Sokoban22Refined85.bonus 28 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 28 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover20 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound21 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 28 p) :
    NetHack.Sokoban22Refined85.bonus 28 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 28 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover21 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound22 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 28 p) :
    NetHack.Sokoban22Refined85.bonus 28 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 28 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover22 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 51), d55894)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local14 p guard decreasing
theorem oracleSound23 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 28 p) :
    NetHack.Sokoban22Refined85.bonus 28 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 28 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover23 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 49), d56147)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local15 p guard decreasing
theorem oracleSound24 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 29 p) :
    NetHack.Sokoban22Refined85.bonus 29 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 29 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover24 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound25 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 29 p) :
    NetHack.Sokoban22Refined85.bonus 29 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 29 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover25 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 51), d56148), ((.push 51 (.stay 73)), d56153)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local16 p guard decreasing
  · subst entry
    exact local17 p guard decreasing
theorem oracleSound26 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 29 p) :
    NetHack.Sokoban22Refined85.bonus 29 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 29 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover26 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 30), d56756)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local18 p guard decreasing
theorem oracleSound27 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 29 p) :
    NetHack.Sokoban22Refined85.bonus 29 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 29 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover27 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 28), d55881), ((.push 28 (.stay 27)), d55749)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local19 p guard decreasing
  · subst entry
    exact local20 p guard decreasing
theorem oracleSound28 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 29 p) :
    NetHack.Sokoban22Refined85.bonus 29 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 29 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover28 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound29 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 29 p) :
    NetHack.Sokoban22Refined85.bonus 29 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 29 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover29 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound30 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 29 p) :
    NetHack.Sokoban22Refined85.bonus 29 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 29 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover30 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 52), d56764)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local21 p guard decreasing
theorem oracleSound31 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 29 p) :
    NetHack.Sokoban22Refined85.bonus 29 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 29 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover31 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 50), d56770)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local22 p guard decreasing
theorem oracleSound32 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 30 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 30 p) :
    NetHack.Sokoban22Refined85.bonus 30 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 30 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover32 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound33 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 30 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 30 p) :
    NetHack.Sokoban22Refined85.bonus 30 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 30 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover33 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 52), d56771), ((.push 52 (.stay 74)), d56776)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local23 p guard decreasing
  · subst entry
    exact local24 p guard decreasing
theorem oracleSound34 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 30 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 30 p) :
    NetHack.Sokoban22Refined85.bonus 30 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 30 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover34 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound35 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 30 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 30 p) :
    NetHack.Sokoban22Refined85.bonus 30 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 30 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover35 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 29), d56756), ((.push 29 (.stay 28)), d55886)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local25 p guard decreasing
  · subst entry
    exact local26 p guard decreasing
theorem oracleSound36 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 30 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 30 p) :
    NetHack.Sokoban22Refined85.bonus 30 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 30 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover36 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound37 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 30 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 30 p) :
    NetHack.Sokoban22Refined85.bonus 30 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 30 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover37 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound38 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 30 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 30 p) :
    NetHack.Sokoban22Refined85.bonus 30 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 30 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover38 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound39 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 30 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 30 p) :
    NetHack.Sokoban22Refined85.bonus 30 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 30 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover39 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 51), d57566)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local27 p guard decreasing
theorem oracleSound40 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 45 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 45 p) :
    NetHack.Sokoban22Refined85.bonus 45 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 45 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover40 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound41 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 45 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 45 p) :
    NetHack.Sokoban22Refined85.bonus 45 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 45 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover41 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 67), d57571), ((.push 67 (.stay 89)), d57576)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local28 p guard decreasing
  · subst entry
    exact local29 p guard decreasing
theorem oracleSound42 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 45 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 45 p) :
    NetHack.Sokoban22Refined85.bonus 45 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 45 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover42 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 46), d58123), ((.push 46 (.stay 47)), d58126)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local30 p guard decreasing
  · subst entry
    exact local31 p guard decreasing
theorem oracleSound43 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 45 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 45 p) :
    NetHack.Sokoban22Refined85.bonus 45 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 45 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover43 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound44 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 45 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 45 p) :
    NetHack.Sokoban22Refined85.bonus 45 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 45 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover44 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound45 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 45 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 45 p) :
    NetHack.Sokoban22Refined85.bonus 45 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 45 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover45 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound46 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 45 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 45 p) :
    NetHack.Sokoban22Refined85.bonus 45 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 45 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover46 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound47 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 45 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 45 p) :
    NetHack.Sokoban22Refined85.bonus 45 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 45 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover47 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound48 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 46 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 46 p) :
    NetHack.Sokoban22Refined85.bonus 46 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 46 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover48 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound49 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 46 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 46 p) :
    NetHack.Sokoban22Refined85.bonus 46 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 46 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover49 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound50 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 46 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 46 p) :
    NetHack.Sokoban22Refined85.bonus 46 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 46 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover50 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 47), d54512), ((.push 47 (.stay 48)), d58129)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local32 p guard decreasing
  · subst entry
    exact local33 p guard decreasing
theorem oracleSound51 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 46 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 46 p) :
    NetHack.Sokoban22Refined85.bonus 46 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 46 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover51 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 45), d58123)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local34 p guard decreasing
theorem oracleSound52 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 46 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 46 p) :
    NetHack.Sokoban22Refined85.bonus 46 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 46 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover52 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 25), d54513)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local35 p guard decreasing
theorem oracleSound53 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 46 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 46 p) :
    NetHack.Sokoban22Refined85.bonus 46 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 46 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover53 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound54 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 46 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 46 p) :
    NetHack.Sokoban22Refined85.bonus 46 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 46 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover54 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 69), d58433)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local36 p guard decreasing
theorem oracleSound55 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 46 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 46 p) :
    NetHack.Sokoban22Refined85.bonus 46 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 46 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover55 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 67), d58745)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local37 p guard decreasing
theorem oracleSound56 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 47 p) :
    NetHack.Sokoban22Refined85.bonus 47 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 47 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover56 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 25), d51640)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local38 p guard decreasing
theorem oracleSound57 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 47 p) :
    NetHack.Sokoban22Refined85.bonus 47 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 47 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover57 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 69), d58432), ((.push 69 (.stay 91)), d58750)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local39 p guard decreasing
  · subst entry
    exact local40 p guard decreasing
theorem oracleSound58 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 47 p) :
    NetHack.Sokoban22Refined85.bonus 47 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 47 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover58 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 48), d54185), ((.push 48 (.stay 49)), d60241)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local41 p guard decreasing
  · subst entry
    exact local42 p guard decreasing
theorem oracleSound59 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 47 p) :
    NetHack.Sokoban22Refined85.bonus 47 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 47 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover59 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 46), d54512), ((.push 46 (.stay 45)), d58126)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local43 p guard decreasing
  · subst entry
    exact local44 p guard decreasing
theorem oracleSound60 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 47 p) :
    NetHack.Sokoban22Refined85.bonus 47 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 47 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover60 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound61 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 47 p) :
    NetHack.Sokoban22Refined85.bonus 47 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 47 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover61 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound62 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 47 p) :
    NetHack.Sokoban22Refined85.bonus 47 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 47 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover62 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 70), d61360)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local45 p guard decreasing
theorem oracleSound63 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 47 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 47 p) :
    NetHack.Sokoban22Refined85.bonus 47 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 47 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover63 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound64 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 48 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 48 p) :
    NetHack.Sokoban22Refined85.bonus 48 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 48 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover64 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound65 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 48 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 48 p) :
    NetHack.Sokoban22Refined85.bonus 48 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 48 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover65 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 70), d61807)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local46 p guard decreasing
theorem oracleSound66 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 48 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 48 p) :
    NetHack.Sokoban22Refined85.bonus 48 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 48 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover66 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 49), d55878), ((.push 49 (.stay 50)), d61810)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local47 p guard decreasing
  · subst entry
    exact local48 p guard decreasing
theorem oracleSound67 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 48 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 48 p) :
    NetHack.Sokoban22Refined85.bonus 48 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 48 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover67 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 47), d54185), ((.push 47 (.stay 46)), d58129)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local49 p guard decreasing
  · subst entry
    exact local50 p guard decreasing
theorem oracleSound68 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 48 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 48 p) :
    NetHack.Sokoban22Refined85.bonus 48 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 48 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover68 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 27), d55879)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local51 p guard decreasing
theorem oracleSound69 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 48 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 48 p) :
    NetHack.Sokoban22Refined85.bonus 48 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 48 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover69 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 25), d54186)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local52 p guard decreasing
theorem oracleSound70 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 48 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 48 p) :
    NetHack.Sokoban22Refined85.bonus 48 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 48 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover70 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 71), d62376)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local53 p guard decreasing
theorem oracleSound71 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 48 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 48 p) :
    NetHack.Sokoban22Refined85.bonus 48 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 48 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover71 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 69), d62827)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local54 p guard decreasing
theorem oracleSound72 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 49 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 49 p) :
    NetHack.Sokoban22Refined85.bonus 49 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 49 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover72 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 27), d54518)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local55 p guard decreasing
theorem oracleSound73 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 49 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 49 p) :
    NetHack.Sokoban22Refined85.bonus 49 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 49 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover73 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 71), d62934), ((.push 71 (.stay 93)), d62939)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local56 p guard decreasing
  · subst entry
    exact local57 p guard decreasing
theorem oracleSound74 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 49 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 49 p) :
    NetHack.Sokoban22Refined85.bonus 49 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 49 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover74 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 50), d55755), ((.push 50 (.stay 51)), d64189)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local58 p guard decreasing
  · subst entry
    exact local59 p guard decreasing
theorem oracleSound75 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 49 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 49 p) :
    NetHack.Sokoban22Refined85.bonus 49 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 49 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover75 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 48), d55878), ((.push 48 (.stay 47)), d60241)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local60 p guard decreasing
  · subst entry
    exact local61 p guard decreasing
theorem oracleSound76 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 49 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 49 p) :
    NetHack.Sokoban22Refined85.bonus 49 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 49 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover76 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 28), d56147)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local62 p guard decreasing
theorem oracleSound77 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 49 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 49 p) :
    NetHack.Sokoban22Refined85.bonus 49 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 49 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover77 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound78 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 49 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 49 p) :
    NetHack.Sokoban22Refined85.bonus 49 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 49 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover78 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound79 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 49 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 49 p) :
    NetHack.Sokoban22Refined85.bonus 49 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 49 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover79 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 70), d64542)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local63 p guard decreasing
end NetHack.Soko22Hazard87
