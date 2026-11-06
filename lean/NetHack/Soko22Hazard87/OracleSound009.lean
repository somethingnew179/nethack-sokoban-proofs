import NetHack.Soko22Hazard87.OracleSound008
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem oracleSound720 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 181 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 181 p) :
    NetHack.Sokoban22Refined85.bonus 181 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 181 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover720 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 159), d163444)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local741 p guard decreasing
theorem oracleSound721 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 181 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 181 p) :
    NetHack.Sokoban22Refined85.bonus 181 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 181 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover721 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound722 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 181 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 181 p) :
    NetHack.Sokoban22Refined85.bonus 181 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 181 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover722 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 182), d211412)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local742 p guard decreasing
theorem oracleSound723 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 181 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 181 p) :
    NetHack.Sokoban22Refined85.bonus 181 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 181 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover723 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 180), d207963)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local743 p guard decreasing
theorem oracleSound724 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 181 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 181 p) :
    NetHack.Sokoban22Refined85.bonus 181 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 181 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover724 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 160), d180907)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local744 p guard decreasing
theorem oracleSound725 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 181 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 181 p) :
    NetHack.Sokoban22Refined85.bonus 181 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 181 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover725 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 158), d162095)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local745 p guard decreasing
theorem oracleSound726 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 181 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 181 p) :
    NetHack.Sokoban22Refined85.bonus 181 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 181 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover726 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 204), d211416)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local746 p guard decreasing
theorem oracleSound727 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 181 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 181 p) :
    NetHack.Sokoban22Refined85.bonus 181 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 181 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover727 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 202), d212559)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local747 p guard decreasing
theorem oracleSound728 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 182 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 182 p) :
    NetHack.Sokoban22Refined85.bonus 182 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 182 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover728 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 160), d169389), ((.push 160 (.stay 138)), d128487)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local748 p guard decreasing
  · subst entry
    exact local749 p guard decreasing
theorem oracleSound729 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 182 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 182 p) :
    NetHack.Sokoban22Refined85.bonus 182 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 182 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover729 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 204), d211415), ((.push 204 (.stay 226)), d216471)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local750 p guard decreasing
  · subst entry
    exact local751 p guard decreasing
theorem oracleSound730 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 182 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 182 p) :
    NetHack.Sokoban22Refined85.bonus 182 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 182 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover730 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound731 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 182 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 182 p) :
    NetHack.Sokoban22Refined85.bonus 182 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 182 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover731 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 181), d211412), ((.push 181 (.stay 180)), d207966)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local752 p guard decreasing
  · subst entry
    exact local753 p guard decreasing
theorem oracleSound732 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 182 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 182 p) :
    NetHack.Sokoban22Refined85.bonus 182 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 182 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover732 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 161), d187678)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local754 p guard decreasing
theorem oracleSound733 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 182 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 182 p) :
    NetHack.Sokoban22Refined85.bonus 182 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 182 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover733 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 159), d169391)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local755 p guard decreasing
theorem oracleSound734 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 182 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 182 p) :
    NetHack.Sokoban22Refined85.bonus 182 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 182 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover734 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound735 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 182 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 182 p) :
    NetHack.Sokoban22Refined85.bonus 182 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 182 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover735 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound736 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 184 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 184 p) :
    NetHack.Sokoban22Refined85.bonus 184 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 184 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover736 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 162), d187679)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local756 p guard decreasing
theorem oracleSound737 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 184 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 184 p) :
    NetHack.Sokoban22Refined85.bonus 184 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 184 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover737 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound738 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 184 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 184 p) :
    NetHack.Sokoban22Refined85.bonus 184 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 184 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover738 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 185), d225586), ((.push 185 (.stay 186)), d225589)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local757 p guard decreasing
  · subst entry
    exact local758 p guard decreasing
theorem oracleSound739 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 184 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 184 p) :
    NetHack.Sokoban22Refined85.bonus 184 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 184 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover739 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound740 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 184 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 184 p) :
    NetHack.Sokoban22Refined85.bonus 184 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 184 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover740 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 163), d192716)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local759 p guard decreasing
theorem oracleSound741 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 184 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 184 p) :
    NetHack.Sokoban22Refined85.bonus 184 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 184 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover741 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 161), d187676)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local760 p guard decreasing
theorem oracleSound742 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 184 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 184 p) :
    NetHack.Sokoban22Refined85.bonus 184 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 184 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover742 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound743 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 184 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 184 p) :
    NetHack.Sokoban22Refined85.bonus 184 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 184 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover743 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound744 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 185 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 185 p) :
    NetHack.Sokoban22Refined85.bonus 185 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 185 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover744 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 163), d190593), ((.push 163 (.stay 141)), d130390)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local761 p guard decreasing
  · subst entry
    exact local762 p guard decreasing
theorem oracleSound745 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 185 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 185 p) :
    NetHack.Sokoban22Refined85.bonus 185 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 185 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover745 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound746 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 185 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 185 p) :
    NetHack.Sokoban22Refined85.bonus 185 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 185 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover746 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 186), d227682)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local763 p guard decreasing
theorem oracleSound747 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 185 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 185 p) :
    NetHack.Sokoban22Refined85.bonus 185 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 185 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover747 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 184), d225586)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local764 p guard decreasing
theorem oracleSound748 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 185 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 185 p) :
    NetHack.Sokoban22Refined85.bonus 185 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 185 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover748 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 164), d194332)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local765 p guard decreasing
theorem oracleSound749 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 185 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 185 p) :
    NetHack.Sokoban22Refined85.bonus 185 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 185 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover749 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 162), d188524)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local766 p guard decreasing
theorem oracleSound750 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 185 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 185 p) :
    NetHack.Sokoban22Refined85.bonus 185 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 185 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover750 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound751 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 185 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 185 p) :
    NetHack.Sokoban22Refined85.bonus 185 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 185 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover751 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound752 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 186 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 186 p) :
    NetHack.Sokoban22Refined85.bonus 186 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 186 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover752 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 164), d192717)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local767 p guard decreasing
theorem oracleSound753 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 186 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 186 p) :
    NetHack.Sokoban22Refined85.bonus 186 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 186 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover753 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound754 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 186 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 186 p) :
    NetHack.Sokoban22Refined85.bonus 186 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 186 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover754 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound755 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 186 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 186 p) :
    NetHack.Sokoban22Refined85.bonus 186 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 186 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover755 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 185), d227682), ((.push 185 (.stay 184)), d225589)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local768 p guard decreasing
  · subst entry
    exact local769 p guard decreasing
theorem oracleSound756 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 186 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 186 p) :
    NetHack.Sokoban22Refined85.bonus 186 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 186 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover756 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound757 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 186 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 186 p) :
    NetHack.Sokoban22Refined85.bonus 186 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 186 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover757 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 163), d192712)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local770 p guard decreasing
theorem oracleSound758 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 186 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 186 p) :
    NetHack.Sokoban22Refined85.bonus 186 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 186 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover758 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound759 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 186 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 186 p) :
    NetHack.Sokoban22Refined85.bonus 186 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 186 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover759 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound760 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 188 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 188 p) :
    NetHack.Sokoban22Refined85.bonus 188 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 188 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover760 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 166), d1), ((.push 166 (.stay 144)), d0)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local771 p guard decreasing
  · subst entry
    exact local772 p guard decreasing
theorem oracleSound761 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 188 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 188 p) :
    NetHack.Sokoban22Refined85.bonus 188 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 188 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover761 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 210), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local773 p guard decreasing
theorem oracleSound762 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 188 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 188 p) :
    NetHack.Sokoban22Refined85.bonus 188 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 188 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover762 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 189), d1), ((.push 189 (.stay 190)), d0)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local774 p guard decreasing
  · subst entry
    exact local775 p guard decreasing
theorem oracleSound763 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 188 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 188 p) :
    NetHack.Sokoban22Refined85.bonus 188 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 188 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover763 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound764 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 188 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 188 p) :
    NetHack.Sokoban22Refined85.bonus 188 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 188 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover764 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 167), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local776 p guard decreasing
theorem oracleSound765 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 188 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 188 p) :
    NetHack.Sokoban22Refined85.bonus 188 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 188 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover765 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound766 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 188 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 188 p) :
    NetHack.Sokoban22Refined85.bonus 188 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 188 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover766 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 211), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local777 p guard decreasing
theorem oracleSound767 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 188 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 188 p) :
    NetHack.Sokoban22Refined85.bonus 188 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 188 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover767 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
theorem oracleSound768 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 189 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 189 p) :
    NetHack.Sokoban22Refined85.bonus 189 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 189 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover768 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 167), d1), ((.push 167 (.stay 145)), d0)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local778 p guard decreasing
  · subst entry
    exact local779 p guard decreasing
theorem oracleSound769 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 189 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 189 p) :
    NetHack.Sokoban22Refined85.bonus 189 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 189 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover769 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 211), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local780 p guard decreasing
theorem oracleSound770 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 189 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 189 p) :
    NetHack.Sokoban22Refined85.bonus 189 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 189 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover770 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 190), d1), ((.push 190 (.stay 191)), d0)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local781 p guard decreasing
  · subst entry
    exact local782 p guard decreasing
theorem oracleSound771 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 189 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 189 p) :
    NetHack.Sokoban22Refined85.bonus 189 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 189 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover771 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 188), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local783 p guard decreasing
theorem oracleSound772 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 189 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 189 p) :
    NetHack.Sokoban22Refined85.bonus 189 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 189 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover772 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 168), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local784 p guard decreasing
theorem oracleSound773 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 189 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 189 p) :
    NetHack.Sokoban22Refined85.bonus 189 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 189 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover773 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 166), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local785 p guard decreasing
theorem oracleSound774 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 189 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 189 p) :
    NetHack.Sokoban22Refined85.bonus 189 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 189 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover774 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 212), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local786 p guard decreasing
theorem oracleSound775 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 189 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 189 p) :
    NetHack.Sokoban22Refined85.bonus 189 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 189 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover775 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 210), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local787 p guard decreasing
theorem oracleSound776 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 190 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 190 p) :
    NetHack.Sokoban22Refined85.bonus 190 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 190 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover776 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 168), d1), ((.push 168 (.stay 146)), d0)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local788 p guard decreasing
  · subst entry
    exact local789 p guard decreasing
theorem oracleSound777 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 190 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 190 p) :
    NetHack.Sokoban22Refined85.bonus 190 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 190 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover777 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 212), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local790 p guard decreasing
theorem oracleSound778 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 190 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 190 p) :
    NetHack.Sokoban22Refined85.bonus 190 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 190 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover778 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 191), d1), ((.push 191 (.stay 192)), d0)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local791 p guard decreasing
  · subst entry
    exact local792 p guard decreasing
theorem oracleSound779 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 190 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 190 p) :
    NetHack.Sokoban22Refined85.bonus 190 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 190 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover779 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 189), d1), ((.push 189 (.stay 188)), d0)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local793 p guard decreasing
  · subst entry
    exact local794 p guard decreasing
theorem oracleSound780 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 190 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 190 p) :
    NetHack.Sokoban22Refined85.bonus 190 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 190 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover780 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 169), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local795 p guard decreasing
theorem oracleSound781 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 190 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 190 p) :
    NetHack.Sokoban22Refined85.bonus 190 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 190 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover781 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 167), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local796 p guard decreasing
theorem oracleSound782 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 190 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 190 p) :
    NetHack.Sokoban22Refined85.bonus 190 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 190 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover782 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 213), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local797 p guard decreasing
theorem oracleSound783 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 190 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 190 p) :
    NetHack.Sokoban22Refined85.bonus 190 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 190 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover783 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 211), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local798 p guard decreasing
theorem oracleSound784 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 191 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 191 p) :
    NetHack.Sokoban22Refined85.bonus 191 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 191 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover784 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 169), d1), ((.push 169 (.stay 147)), d0)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local799 p guard decreasing
  · subst entry
    exact local800 p guard decreasing
theorem oracleSound785 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 191 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 191 p) :
    NetHack.Sokoban22Refined85.bonus 191 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 191 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover785 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 213), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local801 p guard decreasing
theorem oracleSound786 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 191 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 191 p) :
    NetHack.Sokoban22Refined85.bonus 191 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 191 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover786 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 192), d1), ((.push 192 (.stay 193)), d0)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local802 p guard decreasing
  · subst entry
    exact local803 p guard decreasing
theorem oracleSound787 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 191 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 191 p) :
    NetHack.Sokoban22Refined85.bonus 191 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 191 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover787 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 190), d1), ((.push 190 (.stay 189)), d0)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local804 p guard decreasing
  · subst entry
    exact local805 p guard decreasing
theorem oracleSound788 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 191 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 191 p) :
    NetHack.Sokoban22Refined85.bonus 191 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 191 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover788 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 170), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local806 p guard decreasing
theorem oracleSound789 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 191 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 191 p) :
    NetHack.Sokoban22Refined85.bonus 191 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 191 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover789 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 168), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local807 p guard decreasing
theorem oracleSound790 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 191 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 191 p) :
    NetHack.Sokoban22Refined85.bonus 191 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 191 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover790 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 214), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local808 p guard decreasing
theorem oracleSound791 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 191 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 191 p) :
    NetHack.Sokoban22Refined85.bonus 191 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 191 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover791 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 212), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local809 p guard decreasing
theorem oracleSound792 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 192 .north = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 192 p) :
    NetHack.Sokoban22Refined85.bonus 192 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 192 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover792 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 170), d1), ((.push 170 (.stay 148)), d0)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local810 p guard decreasing
  · subst entry
    exact local811 p guard decreasing
theorem oracleSound793 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 192 .south = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 192 p) :
    NetHack.Sokoban22Refined85.bonus 192 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 192 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover793 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 214), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local812 p guard decreasing
theorem oracleSound794 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 192 .east = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 192 p) :
    NetHack.Sokoban22Refined85.bonus 192 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 192 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover794 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 193), d1), ((.push 193 (.stay 194)), d0)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local813 p guard decreasing
  · subst entry
    exact local814 p guard decreasing
theorem oracleSound795 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 192 .west = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 192 p) :
    NetHack.Sokoban22Refined85.bonus 192 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 192 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover795 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 191), d1), ((.push 191 (.stay 190)), d0)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same|same
  · subst entry
    exact local815 p guard decreasing
  · subst entry
    exact local816 p guard decreasing
theorem oracleSound796 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 192 .northEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 192 p) :
    NetHack.Sokoban22Refined85.bonus 192 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 192 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover796 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 171), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local817 p guard decreasing
theorem oracleSound797 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 192 .northWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 192 p) :
    NetHack.Sokoban22Refined85.bonus 192 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 192 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover797 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 169), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local818 p guard decreasing
theorem oracleSound798 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 192 .southEast = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 192 p) :
    NetHack.Sokoban22Refined85.bonus 192 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 192 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover798 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 215), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local819 p guard decreasing
theorem oracleSound799 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 192 .southWest = some outcome)
    (decreasing : bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) < bonus 192 p) :
    NetHack.Sokoban22Refined85.bonus 192 (HazardPattern.boxes ClosedComponents.soko2_2Support p) + bonus 192 p ≤
      HazardPattern.slack Generated.soko2_2Potential outcome + NetHack.Sokoban22Refined85.bonus (HazardPattern.nextHero outcome) (HazardPattern.boxes ClosedComponents.soko2_2Support (HazardPattern.afterPattern 10000 p outcome)) + bonus (HazardPattern.nextHero outcome) (HazardPattern.afterPattern 10000 p outcome) := by
  rcases oracleCover799 p outcome checked with ⟨entry, member, same, guard⟩
  subst outcome
  change entry ∈ ([((.walk 213), d1)] : List OracleBranch) at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same
  · subst entry
    exact local820 p guard decreasing
end NetHack.Soko22Hazard87
