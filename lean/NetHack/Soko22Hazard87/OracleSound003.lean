import NetHack.Soko22Hazard87.OracleSound002
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem oracleSound240 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 93 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 93 p) :
    NetHack.Sokoban22Refined85.bonus 93 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 93 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover240 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 71), d73492), ((.push 71 (.stay 49)), d62939)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local206 p guard decreasing
  · subst entry
    exact local207 p guard decreasing
theorem oracleSound241 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 93 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 93 p) :
    NetHack.Sokoban22Refined85.bonus 93 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 93 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover241 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 115), d82320)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local208 p guard decreasing
theorem oracleSound242 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 93 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 93 p) :
    NetHack.Sokoban22Refined85.bonus 93 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 93 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover242 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 94), d82321), ((.push 94 (.stay 95)), d82324)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local209 p guard decreasing
  · subst entry
    exact local210 p guard decreasing
theorem oracleSound243 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 93 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 93 p) :
    NetHack.Sokoban22Refined85.bonus 93 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 93 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover243 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound244 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 93 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 93 p) :
    NetHack.Sokoban22Refined85.bonus 93 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 93 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover244 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound245 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 93 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 93 p) :
    NetHack.Sokoban22Refined85.bonus 93 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 93 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover245 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 70), d73493)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local211 p guard decreasing
theorem oracleSound246 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 93 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 93 p) :
    NetHack.Sokoban22Refined85.bonus 93 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 93 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover246 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 116), d82333)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local212 p guard decreasing
theorem oracleSound247 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 93 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 93 p) :
    NetHack.Sokoban22Refined85.bonus 93 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 93 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover247 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 114), d82334)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local213 p guard decreasing
theorem oracleSound248 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 94 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 94 p) :
    NetHack.Sokoban22Refined85.bonus 94 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 94 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover248 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound249 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 94 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 94 p) :
    NetHack.Sokoban22Refined85.bonus 94 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 94 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover249 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 116), d82335), ((.push 116 (.stay 138)), d82340)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local214 p guard decreasing
  · subst entry
    exact local215 p guard decreasing
theorem oracleSound250 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 94 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 94 p) :
    NetHack.Sokoban22Refined85.bonus 94 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 94 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover250 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 95), d82347), ((.push 95 (.stay 96)), d82350)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local216 p guard decreasing
  · subst entry
    exact local217 p guard decreasing
theorem oracleSound251 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 94 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 94 p) :
    NetHack.Sokoban22Refined85.bonus 94 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 94 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover251 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 93), d82321)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local218 p guard decreasing
theorem oracleSound252 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 94 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 94 p) :
    NetHack.Sokoban22Refined85.bonus 94 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 94 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover252 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 73), d74047)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local219 p guard decreasing
theorem oracleSound253 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 94 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 94 p) :
    NetHack.Sokoban22Refined85.bonus 94 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 94 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover253 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 71), d74039)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local220 p guard decreasing
theorem oracleSound254 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 94 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 94 p) :
    NetHack.Sokoban22Refined85.bonus 94 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 94 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover254 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound255 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 94 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 94 p) :
    NetHack.Sokoban22Refined85.bonus 94 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 94 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover255 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 115), d82355)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local221 p guard decreasing
theorem oracleSound256 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 95 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 95 p) :
    NetHack.Sokoban22Refined85.bonus 95 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 95 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover256 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 73), d74040), ((.push 73 (.stay 51)), d65090)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local222 p guard decreasing
  · subst entry
    exact local223 p guard decreasing
theorem oracleSound257 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 95 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 95 p) :
    NetHack.Sokoban22Refined85.bonus 95 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 95 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover257 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound258 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 95 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 95 p) :
    NetHack.Sokoban22Refined85.bonus 95 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 95 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover258 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 96), d74044), ((.push 96 (.stay 97)), d82357)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local224 p guard decreasing
  · subst entry
    exact local225 p guard decreasing
theorem oracleSound259 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 95 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 95 p) :
    NetHack.Sokoban22Refined85.bonus 95 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 95 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover259 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 94), d82347), ((.push 94 (.stay 93)), d82324)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local226 p guard decreasing
  · subst entry
    exact local227 p guard decreasing
theorem oracleSound260 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 95 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 95 p) :
    NetHack.Sokoban22Refined85.bonus 95 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 95 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover260 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 74), d74062)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local228 p guard decreasing
theorem oracleSound261 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 95 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 95 p) :
    NetHack.Sokoban22Refined85.bonus 95 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 95 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover261 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound262 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 95 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 95 p) :
    NetHack.Sokoban22Refined85.bonus 95 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 95 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover262 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 118), d82360)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local229 p guard decreasing
theorem oracleSound263 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 95 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 95 p) :
    NetHack.Sokoban22Refined85.bonus 95 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 95 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover263 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 116), d82362)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local230 p guard decreasing
theorem oracleSound264 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 96 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 96 p) :
    NetHack.Sokoban22Refined85.bonus 96 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 96 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover264 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 74), d74048), ((.push 74 (.stay 52)), d66280)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local231 p guard decreasing
  · subst entry
    exact local232 p guard decreasing
theorem oracleSound265 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 96 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 96 p) :
    NetHack.Sokoban22Refined85.bonus 96 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 96 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover265 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 118), d82363)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local233 p guard decreasing
theorem oracleSound266 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 96 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 96 p) :
    NetHack.Sokoban22Refined85.bonus 96 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 96 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover266 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 97), d82364), ((.push 97 (.stay 98)), d82367)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local234 p guard decreasing
  · subst entry
    exact local235 p guard decreasing
theorem oracleSound267 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 96 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 96 p) :
    NetHack.Sokoban22Refined85.bonus 96 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 96 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover267 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 95), d74044), ((.push 95 (.stay 94)), d82350)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local236 p guard decreasing
  · subst entry
    exact local237 p guard decreasing
theorem oracleSound268 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 96 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 96 p) :
    NetHack.Sokoban22Refined85.bonus 96 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 96 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover268 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound269 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 96 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 96 p) :
    NetHack.Sokoban22Refined85.bonus 96 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 96 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover269 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 73), d74046)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local238 p guard decreasing
theorem oracleSound270 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 96 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 96 p) :
    NetHack.Sokoban22Refined85.bonus 96 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 96 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover270 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 119), d82375)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local239 p guard decreasing
theorem oracleSound271 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 96 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 96 p) :
    NetHack.Sokoban22Refined85.bonus 96 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 96 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover271 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound272 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 97 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 97 p) :
    NetHack.Sokoban22Refined85.bonus 97 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 97 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover272 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound273 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 97 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 97 p) :
    NetHack.Sokoban22Refined85.bonus 97 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 97 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover273 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 119), d82376), ((.push 119 (.stay 141)), d82381)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local240 p guard decreasing
  · subst entry
    exact local241 p guard decreasing
theorem oracleSound274 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 97 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 97 p) :
    NetHack.Sokoban22Refined85.bonus 97 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 97 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover274 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 98), d74073)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local242 p guard decreasing
theorem oracleSound275 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 97 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 97 p) :
    NetHack.Sokoban22Refined85.bonus 97 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 97 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover275 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 96), d82364), ((.push 96 (.stay 95)), d82357)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local243 p guard decreasing
  · subst entry
    exact local244 p guard decreasing
theorem oracleSound276 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 97 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 97 p) :
    NetHack.Sokoban22Refined85.bonus 97 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 97 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover276 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 76), d74074)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local245 p guard decreasing
theorem oracleSound277 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 97 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 97 p) :
    NetHack.Sokoban22Refined85.bonus 97 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 97 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover277 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 74), d74056)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local246 p guard decreasing
theorem oracleSound278 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 97 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 97 p) :
    NetHack.Sokoban22Refined85.bonus 97 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 97 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover278 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 120), d82409)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local247 p guard decreasing
theorem oracleSound279 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 97 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 97 p) :
    NetHack.Sokoban22Refined85.bonus 97 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 97 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover279 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 118), d82414)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local248 p guard decreasing
theorem oracleSound280 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 98 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 98 p) :
    NetHack.Sokoban22Refined85.bonus 98 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 98 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover280 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 76), d74067)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local249 p guard decreasing
theorem oracleSound281 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 98 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 98 p) :
    NetHack.Sokoban22Refined85.bonus 98 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 98 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover281 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 120), d82415)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local250 p guard decreasing
theorem oracleSound282 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 98 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 98 p) :
    NetHack.Sokoban22Refined85.bonus 98 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 98 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover282 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound283 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 98 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 98 p) :
    NetHack.Sokoban22Refined85.bonus 98 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 98 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover283 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 97), d74073), ((.push 97 (.stay 96)), d82367)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local251 p guard decreasing
  · subst entry
    exact local252 p guard decreasing
theorem oracleSound284 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 98 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 98 p) :
    NetHack.Sokoban22Refined85.bonus 98 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 98 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover284 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound285 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 98 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 98 p) :
    NetHack.Sokoban22Refined85.bonus 98 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 98 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover285 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound286 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 98 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 98 p) :
    NetHack.Sokoban22Refined85.bonus 98 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 98 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover286 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound287 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 98 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 98 p) :
    NetHack.Sokoban22Refined85.bonus 98 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 98 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover287 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 119), d82422)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local253 p guard decreasing
theorem oracleSound288 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 100 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 100 p) :
    NetHack.Sokoban22Refined85.bonus 100 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 100 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover288 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 78), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local254 p guard decreasing
theorem oracleSound289 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 100 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 100 p) :
    NetHack.Sokoban22Refined85.bonus 100 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 100 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover289 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 122), d1), ((.push 122 (.stay 144)), d0)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local255 p guard decreasing
  · subst entry
    exact local256 p guard decreasing
theorem oracleSound290 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 100 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 100 p) :
    NetHack.Sokoban22Refined85.bonus 100 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 100 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover290 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 101), d1), ((.push 101 (.stay 102)), d0)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local257 p guard decreasing
  · subst entry
    exact local258 p guard decreasing
theorem oracleSound291 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 100 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 100 p) :
    NetHack.Sokoban22Refined85.bonus 100 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 100 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover291 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound292 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 100 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 100 p) :
    NetHack.Sokoban22Refined85.bonus 100 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 100 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover292 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 79), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local259 p guard decreasing
theorem oracleSound293 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 100 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 100 p) :
    NetHack.Sokoban22Refined85.bonus 100 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 100 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover293 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound294 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 100 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 100 p) :
    NetHack.Sokoban22Refined85.bonus 100 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 100 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover294 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 123), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local260 p guard decreasing
theorem oracleSound295 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 100 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 100 p) :
    NetHack.Sokoban22Refined85.bonus 100 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 100 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover295 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound296 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 101 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 101 p) :
    NetHack.Sokoban22Refined85.bonus 101 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 101 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover296 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 79), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local261 p guard decreasing
theorem oracleSound297 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 101 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 101 p) :
    NetHack.Sokoban22Refined85.bonus 101 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 101 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover297 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 123), d1), ((.push 123 (.stay 145)), d0)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local262 p guard decreasing
  · subst entry
    exact local263 p guard decreasing
theorem oracleSound298 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 101 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 101 p) :
    NetHack.Sokoban22Refined85.bonus 101 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 101 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover298 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 102), d1), ((.push 102 (.stay 103)), d0)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local264 p guard decreasing
  · subst entry
    exact local265 p guard decreasing
theorem oracleSound299 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 101 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 101 p) :
    NetHack.Sokoban22Refined85.bonus 101 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 101 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover299 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 100), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local266 p guard decreasing
theorem oracleSound300 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 101 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 101 p) :
    NetHack.Sokoban22Refined85.bonus 101 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 101 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover300 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 80), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local267 p guard decreasing
theorem oracleSound301 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 101 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 101 p) :
    NetHack.Sokoban22Refined85.bonus 101 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 101 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover301 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 78), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local268 p guard decreasing
theorem oracleSound302 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 101 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 101 p) :
    NetHack.Sokoban22Refined85.bonus 101 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 101 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover302 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 124), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local269 p guard decreasing
theorem oracleSound303 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 101 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 101 p) :
    NetHack.Sokoban22Refined85.bonus 101 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 101 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover303 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 122), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local270 p guard decreasing
theorem oracleSound304 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 102 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 102 p) :
    NetHack.Sokoban22Refined85.bonus 102 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 102 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover304 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 80), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local271 p guard decreasing
theorem oracleSound305 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 102 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 102 p) :
    NetHack.Sokoban22Refined85.bonus 102 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 102 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover305 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 124), d1), ((.push 124 (.stay 146)), d0)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local272 p guard decreasing
  · subst entry
    exact local273 p guard decreasing
theorem oracleSound306 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 102 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 102 p) :
    NetHack.Sokoban22Refined85.bonus 102 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 102 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover306 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 103), d1), ((.push 103 (.stay 104)), d0)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local274 p guard decreasing
  · subst entry
    exact local275 p guard decreasing
theorem oracleSound307 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 102 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 102 p) :
    NetHack.Sokoban22Refined85.bonus 102 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 102 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover307 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 101), d1), ((.push 101 (.stay 100)), d0)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local276 p guard decreasing
  · subst entry
    exact local277 p guard decreasing
theorem oracleSound308 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 102 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 102 p) :
    NetHack.Sokoban22Refined85.bonus 102 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 102 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover308 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 81), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local278 p guard decreasing
theorem oracleSound309 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 102 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 102 p) :
    NetHack.Sokoban22Refined85.bonus 102 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 102 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover309 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 79), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local279 p guard decreasing
theorem oracleSound310 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 102 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 102 p) :
    NetHack.Sokoban22Refined85.bonus 102 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 102 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover310 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 125), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local280 p guard decreasing
theorem oracleSound311 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 102 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 102 p) :
    NetHack.Sokoban22Refined85.bonus 102 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 102 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover311 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 123), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local281 p guard decreasing
theorem oracleSound312 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 103 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 103 p) :
    NetHack.Sokoban22Refined85.bonus 103 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 103 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover312 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 81), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local282 p guard decreasing
theorem oracleSound313 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 103 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 103 p) :
    NetHack.Sokoban22Refined85.bonus 103 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 103 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover313 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 125), d1), ((.push 125 (.stay 147)), d0)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local283 p guard decreasing
  · subst entry
    exact local284 p guard decreasing
theorem oracleSound314 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 103 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 103 p) :
    NetHack.Sokoban22Refined85.bonus 103 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 103 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover314 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 104), d1), ((.push 104 (.stay 105)), d0)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local285 p guard decreasing
  · subst entry
    exact local286 p guard decreasing
theorem oracleSound315 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 103 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 103 p) :
    NetHack.Sokoban22Refined85.bonus 103 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 103 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover315 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 102), d1), ((.push 102 (.stay 101)), d0)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local287 p guard decreasing
  · subst entry
    exact local288 p guard decreasing
theorem oracleSound316 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 103 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 103 p) :
    NetHack.Sokoban22Refined85.bonus 103 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 103 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover316 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 82), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local289 p guard decreasing
theorem oracleSound317 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 103 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 103 p) :
    NetHack.Sokoban22Refined85.bonus 103 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 103 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover317 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 80), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local290 p guard decreasing
theorem oracleSound318 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 103 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 103 p) :
    NetHack.Sokoban22Refined85.bonus 103 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 103 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover318 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 126), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local291 p guard decreasing
theorem oracleSound319 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 103 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 103 p) :
    NetHack.Sokoban22Refined85.bonus 103 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 103 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover319 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 124), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local292 p guard decreasing
end NetHack.Soko22Hazard87
