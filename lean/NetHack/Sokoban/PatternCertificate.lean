import NetHack.Sokoban.PatternProjection
import NetHack.Sokoban.PatternRows
import NetHack.Sokoban.PatternEdges
import NetHack.Sokoban.PatternChecks
import NetHack.Sokoban.PatternGoals
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.PatternCertificate
open LowerBounds
theorem rowFacts_sound (edge : Edge) (member : edge ∈ edges) :
    advance soko4_2.board edge.player edge.direction = some edge.source ∧
    advance soko4_2.board edge.source edge.direction = some edge.first ∧
    edge.moveSlack = 1 + Generated.soko4_2Potential.boulder edge.landing - Generated.soko4_2Potential.boulder edge.source ∧
    edge.consumeSlack = 1 - Generated.soko4_2Potential.boulder edge.source - Generated.soko4_2Potential.hole edge.landing :=
  of_decide_eq_true (List.all_eq_true.mp rowFacts_checked edge member)

theorem coverage_sound (player source : Cell) (direction : Dir) (landing : Cell)
    (playerFloor : player ∈ soko4_2.board.floor)
    (sourceFloor : source ∈ soko4_2.board.floor)
    (adjacent : advance soko4_2.board player direction = some source)
    (landingMember : landing ∈ pushTargets soko4_2.board source direction) :
    ∃ edge ∈ edges, edge.player = player ∧ edge.source = source ∧
      edge.direction = direction ∧ edge.landing = landing := by
  let chosen := computedEdge player source direction landing
  have floorTrue : soko4_2.board.floor.contains source = true := List.contains_iff_mem.mpr sourceFloor
  have member : chosen ∈ computedEdges := by
    apply List.mem_flatMap.mpr
    refine ⟨player, playerFloor, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨direction, checkedDirs_complete direction, ?_⟩
    simpa only [adjacent, floorTrue, Bool.not_true, Bool.false_eq_true, ↓reduceIte] using
      (List.mem_map.mpr ⟨landing, landingMember, rfl⟩ : chosen ∈
        (pushTargets soko4_2.board source direction).map (computedEdge player source direction))
  exact ⟨chosen, edges_exact.symm ▸ member, rfl, rfl, rfl, rfl⟩

theorem bool_member (value : Bool) : value ∈ [false,true] := by
  cases value <;> simp

theorem pattern_member (pattern : Nine) : pattern ∈ allPatterns := by
  cases pattern with
  | mk a b c d e f g h i =>
    simp only [allPatterns, List.mem_flatMap, List.mem_singleton]
    exact ⟨a, bool_member a, b, bool_member b, c, bool_member c, d, bool_member d,
      e, bool_member e, f, bool_member f, g, bool_member g, h, bool_member h, i, bool_member i, rfl⟩

theorem pattern_checked (pattern : Nine) : activeEdges.all (rowCheck pattern) = true :=
  List.all_eq_true.mp all_patterns_checked pattern (pattern_member pattern)

theorem local_bounds (pattern : Nine) (player source : Cell) (direction : Dir) (landing : Cell)
    (playerFloor : player ∈ soko4_2.board.floor)
    (sourceFloor : source ∈ soko4_2.board.floor)
    (adjacent : advance soko4_2.board player direction = some source)
    (landingMember : landing ∈ pushTargets soko4_2.board source direction)
    (playerClear : known pattern player = false)
    (firstClear : ∀ first, advance soko4_2.board source direction = some first → known pattern first = false)
    (landingClear : landing = source ∨ known pattern landing = false) :
    (bonus pattern ≤ (1 + Generated.soko4_2Potential.boulder landing - Generated.soko4_2Potential.boulder source) +
      bonus (insert (erase pattern source) landing)) ∧
    (bonus pattern ≤ (1 - Generated.soko4_2Potential.boulder source - Generated.soko4_2Potential.hole landing) +
      bonus (erase pattern source)) := by
  by_cases active : source ∈ support
  ·
    rcases coverage_sound player source direction landing playerFloor sourceFloor adjacent landingMember with
      ⟨edge, member, playerEq, sourceEq, directionEq, landingEq⟩
    have facts := rowFacts_sound edge member
    have edgeFirst : advance soko4_2.board source direction = some edge.first := by
      simpa [sourceEq, directionEq] using facts.2.1
    have firstFalse := firstClear edge.first edgeFirst
    have selected : edge ∈ activeEdges := by
      rw [active_exact]
      exact List.mem_filter.mpr ⟨member, by simpa only [sourceEq] using (List.contains_iff_mem.mpr active : support.contains source = true)⟩
    have checked := List.all_eq_true.mp (pattern_checked pattern) edge selected
    have guardFalse : (known pattern edge.player || known pattern edge.first ||
        (known pattern edge.landing && decide (edge.landing ≠ edge.source))) = false := by
      rcases landingClear with same | clear
      · simp [playerEq, sourceEq, landingEq, playerClear, firstFalse, same]
      · simp [playerEq, sourceEq, landingEq, playerClear, firstFalse, clear]
    have paired : (decide (bonus pattern ≤ edge.moveSlack + bonus (insert (erase pattern edge.source) edge.landing)) &&
        decide (bonus pattern ≤ edge.consumeSlack + bonus (erase pattern edge.source))) = true := by
      simpa only [rowCheck, guardFalse, Bool.false_eq_true, ↓reduceIte] using checked
    have checked := Bool.and_eq_true_iff.mp paired
    constructor
    · have bound := of_decide_eq_true checked.1
      simpa [facts.2.2.1, sourceEq, landingEq] using bound
    · have bound := of_decide_eq_true checked.2
      simpa [facts.2.2.2, sourceEq, landingEq] using bound
  · have unchanged := PatternProjection.outside_bonus_bounds pattern source landing active
    have edge := Generated.soko4_2_potential_valid.edge source sourceFloor direction landing landingMember
    have absorption := Generated.soko4_2_potential_valid.absorption landing
    constructor <;> omega


theorem goal_pattern (pattern : Nine) :
    bonus pattern ≤ weightSum debt (occupied pattern) + max 0 (Int.ofNat (occupied pattern).length - 2) := by
  exact of_decide_eq_true (List.all_eq_true.mp all_goals_checked pattern (pattern_member pattern))

theorem support_nodup : support.Nodup := by decide

end NetHack.Sokoban.PatternCertificate
