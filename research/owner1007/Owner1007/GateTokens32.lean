import Owner1007.TokenBounds32
import Owner1007.Heavy32

namespace Owner1007.GateTokens32
open NetHack.Sokoban NetHack.Sokoban.LowerBounds
open NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open NetHack.Sokoban.GhostProjection Owner1007.TokenAccounting Owner1007.Heavy32

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem blocked139_checked :
    ∀ hero ∈ soko3_2.board.floor, ∀ dir ∈ allDirs,
      advance soko3_2.board hero dir = some 139 →
      hero = 113 ∨ BlockedPush soko3_2.board [113] 139 dir := by decide +kernel

theorem blocked139_head {state : State} {dir : Dir} {t : Transition}
    (checked : step soko3_2.board state dir = some t)
    {result : Ending} (effect : Matches state t (.push 139 result))
    (occupied : 113 ∈ state.boulders) : False := by
  have pushed : t.pushed = true := by
    cases result with
    | stay landing => simp only [effect.2]
    | fill hole => simp only [effect.2.2]
  rcases step_cases_full soko3_2.board state dir t checked with walked | pushedCase
  · obtain ⟨target, _, _, _, _, shape⟩ := walked
    simp only [shape] at pushed
    contradiction
  · obtain ⟨source, res, adjacent, _, _, push, shape⟩ := pushedCase
    have actualHero : t.state.player = source := by
      simpa only [shape] using (show t.state.player = t.state.player from rfl)
    have same : source = 139 := actualHero.symm.trans (matches_hero state t (.push 139 result) effect)
    rw [same] at push adjacent
    have clear := step_player_clear _ _ _ _ checked
    have first := push_first_clear soko3_2.board state 139 dir res push
    have blocked := blocked139_checked state.player clear.1 dir (Geometry.all_directions dir) adjacent
    rcases blocked with hero | blocked
    · exact clear.2.2.1 (hero ▸ occupied)
    · rcases blocked with diagonal | blocked
      · simp [first.1] at diagonal
      · obtain ⟨dest, next, floor, door, empty⟩ := first.2
        simp only [next] at blocked
        rcases blocked with wall | door' | box
        · exact wall floor
        · exact door door'
        · have destEq : dest = 113 := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using box
          exact empty (destEq ▸ occupied)

theorem fixed113_blocks139 {state final : State} {dirs : List Dir} {pushes moves : Nat}
    {outcomes : List Outcome}
    (logged : Logged soko3_2.board state dirs final pushes moves outcomes)
    (occupied : 113 ∈ state.boulders)
    (fixed : ownPushes [113] outcomes = 0) : ownPushes [139] outcomes = 0 := by
  induction logged with
  | nil current => rfl
  | @cons state dir t rest final pushes moves outcome outcomes head effect tail ih =>
    have first113 : ownPush [113] outcome = 0 := by simp only [ownPushes] at fixed; omega
    have update113 := ownPush_zero_update [113] outcome first113
    have rest113 : ownPushes [113] outcomes = 0 := by
      simp only [ownPushes, first113, update113, Nat.zero_add] at fixed
      exact fixed
    have subset113 : [113] ⊆ state.boulders := by
      intro c member
      have eq : c = 113 := by simpa using member
      subst c
      exact occupied
    have after113 := GhostSubset.update_subset state t outcome effect [113] (by simp) subset113
    rw [update113] at after113
    have occupiedNext : 113 ∈ t.state.boulders := after113 (by simp)
    have first139 : ownPush [139] outcome = 0 := by
      cases outcome with
      | walk target => rfl
      | push source result =>
        by_cases own : source = 139
        · subst source
          exact False.elim (blocked139_head head effect occupied)
        · simp [ownPush, own]
    have update139 := ownPush_zero_update [139] outcome first139
    have rest139 := ih occupiedNext rest113
    simp only [ownPushes, first139, update139, Nat.zero_add, rest139]

theorem zero113 : ∀ r ∈ NetHack.Soko32SAT.Frames.stays, r.source = 113 →
    ss r = 0 → r.hero = 114 ∧ r.direction = .west ∧ r.landing = 112 := by decide +kernel
theorem zero112 : ∀ r ∈ NetHack.Soko32SAT.Frames.stays, r.source = 112 →
    ss r = 0 → r.hero = 86 ∧ r.direction = .south ∧ r.landing = 138 := by decide +kernel
theorem zero86 : ∀ r ∈ NetHack.Soko32SAT.Frames.stays, r.source = 86 →
    ss r = 0 → r.hero = 60 ∧ r.direction = .south ∧ r.landing = 112 := by decide +kernel

theorem zero_head113 {state : State} {history : List Dir} {past pastMoves : Nat}
    (reached : Trace soko3_2.board soko3_2.initial history state past pastMoves)
    {dir : Dir} {t : Transition} (checked : step soko3_2.board state dir = some t)
    {result : Ending} (effect : Matches state t (.push 113 result))
    (zero : slack p (.push 113 result) = 0) :
    result = .stay 112 ∧ state.player = 114 ∧ dir = .west := by
  obtain ⟨_, _, covered⟩ := covered_head reached checked effect
  cases result with
  | stay landing =>
    obtain ⟨row, member, heroEq, sourceEq, dirEq, landingEq⟩ := covered
    have cost : ss row = 0 := by simpa only [ss, sourceEq, landingEq, slack] using zero
    have found := zero113 row member sourceEq cost
    refine ⟨?_, heroEq.symm.trans found.1, dirEq.symm.trans found.2.1⟩
    rw [←landingEq, found.2.2]
  | fill hole => have wrong : (113 : Nat) = 270 := covered.2.1; omega

theorem zero_head112 {state : State} {history : List Dir} {past pastMoves : Nat}
    (reached : Trace soko3_2.board soko3_2.initial history state past pastMoves)
    {dir : Dir} {t : Transition} (checked : step soko3_2.board state dir = some t)
    {result : Ending} (effect : Matches state t (.push 112 result))
    (zero : slack p (.push 112 result) = 0) :
    result = .stay 138 ∧ state.player = 86 ∧ dir = .south := by
  obtain ⟨_, _, covered⟩ := covered_head reached checked effect
  cases result with
  | stay landing =>
    obtain ⟨row, member, heroEq, sourceEq, dirEq, landingEq⟩ := covered
    have cost : ss row = 0 := by simpa only [ss, sourceEq, landingEq, slack] using zero
    have found := zero112 row member sourceEq cost
    refine ⟨?_, heroEq.symm.trans found.1, dirEq.symm.trans found.2.1⟩
    rw [←landingEq, found.2.2]
  | fill hole => have wrong : (112 : Nat) = 270 := covered.2.1; omega

theorem zero_head86 {state : State} {history : List Dir} {past pastMoves : Nat}
    (reached : Trace soko3_2.board soko3_2.initial history state past pastMoves)
    {dir : Dir} {t : Transition} (checked : step soko3_2.board state dir = some t)
    {result : Ending} (effect : Matches state t (.push 86 result))
    (zero : slack p (.push 86 result) = 0) :
    result = .stay 112 ∧ state.player = 60 ∧ dir = .south := by
  obtain ⟨_, _, covered⟩ := covered_head reached checked effect
  cases result with
  | stay landing =>
    obtain ⟨row, member, heroEq, sourceEq, dirEq, landingEq⟩ := covered
    have cost : ss row = 0 := by simpa only [ss, sourceEq, landingEq, slack] using zero
    have found := zero86 row member sourceEq cost
    refine ⟨?_, heroEq.symm.trans found.1, dirEq.symm.trans found.2.1⟩
    rw [←landingEq, found.2.2]
  | fill hole => have wrong : (86 : Nat) = 270 := covered.2.1; omega

#print axioms fixed113_blocks139
#print axioms zero_head113
#print axioms zero_head112
#print axioms zero_head86
end Owner1007.GateTokens32
