import Owner1007.PricedCorral11
import NetHack.Sokoban.Reduction

namespace Owner1007.FirstSplit12
open NetHack.Sokoban NetHack.Sokoban.HazardPattern
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def firstRegion : List Cell := [370,396,397]
def atHero (hero : Cell) : State := {soko1_2.initial with player := hero}
def afterN : State := {player := 371, boulders := 345 :: soko1_2.initial.boulders.erase 371, holes := soko1_2.initial.holes}
def afterE : State := {player := 371, boulders := 372 :: soko1_2.initial.boulders.erase 371, holes := soko1_2.initial.holes}

theorem first_step_cases :
    ∀ hero ∈ firstRegion, ∀ dir ∈ allDirs,
      ∀ t ∈ (step soko1_2.board (atHero hero) dir).toList,
      (t.pushCost = 0 ∧ t.state.boulders = soko1_2.initial.boulders ∧
        t.state.holes = soko1_2.initial.holes ∧ t.state.player ∈ firstRegion) ∨
      (t.pushCost = 1 ∧ (t.state = afterN ∨ t.state = afterE)) := by decide +kernel

/-- Arbitrary walking prefixes are allowed; the first push has only these two outcomes. -/
theorem first_push_split {state final : State} {dirs : List Dir} {pushes moves : Nat}
    (trace : Trace soko1_2.board state dirs final pushes moves)
    (boxes : state.boulders = soko1_2.initial.boulders)
    (holes : state.holes = soko1_2.initial.holes) (hero : state.player ∈ firstRegion)
    (completed : Goal final) :
    ∃ suffixPushes suffixMoves suffixDirs,
      pushes = 1 + suffixPushes ∧
      (Trace soko1_2.board afterN suffixDirs final suffixPushes suffixMoves ∨
       Trace soko1_2.board afterE suffixDirs final suffixPushes suffixMoves) := by
  induction trace with
  | nil current =>
    have empty : soko1_2.initial.holes = [] := holes.symm.trans completed
    have notEmpty : soko1_2.initial.holes ≠ [] := by decide +kernel
    exact False.elim (notEmpty empty)
  | @cons state dir t rest final pushes moves head tail ih =>
    have canonical : state = atHero state.player := by
      cases state
      simp_all [atHero]
    have member : t ∈ (step soko1_2.board (atHero state.player) dir).toList := by
      rw [←canonical, head]
      simp
    rcases first_step_cases state.player hero dir (Geometry.all_directions dir) t member with walk | push
    · obtain ⟨cost, nextBoxes, nextHoles, nextHero⟩ := walk
      obtain ⟨p, m, ds, count, branch⟩ := ih nextBoxes nextHoles nextHero completed
      exact ⟨p, m, ds, by omega, branch⟩
    · obtain ⟨cost, shape⟩ := push
      refine ⟨pushes, moves, rest, by omega, ?_⟩
      rcases shape with north | east
      · exact Or.inl (by rw [←north]; exact tail)
      · exact Or.inr (by rw [←east]; exact tail)

theorem original_first_push_split {dirs final pushes moves}
    (trace : Trace soko1_2.board soko1_2.initial dirs final pushes moves)
    (completed : Goal final) :
    ∃ suffixPushes suffixMoves suffixDirs,
      pushes = 1 + suffixPushes ∧
      (Trace soko1_2.board afterN suffixDirs final suffixPushes suffixMoves ∨
       Trace soko1_2.board afterE suffixDirs final suffixPushes suffixMoves) :=
  first_push_split trace rfl rfl (by decide +kernel) completed

#print axioms original_first_push_split
end Owner1007.FirstSplit12
