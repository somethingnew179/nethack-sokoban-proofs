/- A successful original collision-free push has exactly the same result
after removing an arbitrary subset of OTHER boulders. Tracked boulders may
not disappear at a spatial-window boundary. Walls, doors, RLT, first hazard
consumption and the actual initiated-push cost remain unchanged. -/
import NetHack.Sokoban.GhostPartitionBound
import NetHack.Sokoban.HeroPhasePotential.SmallPattern

namespace NetHack.Sokoban.GhostProjection
open HazardPattern PatternCorrection
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem clear_of_subset (small large : Pattern)
    (subset : ∀ cell, small cell = true → large cell = true)
    (cell : Cell) (clear : large cell = false) : small cell = false := by
  cases found : small cell with
  | false => rfl
  | true => have impossible := subset cell found; rw [clear] at impossible; cases impossible

theorem erase_subset (small large : Pattern)
    (subset : ∀ cell, small cell = true → large cell = true) (source : Cell) :
    ∀ cell, change small source none cell = true → change large source none cell = true := by
  intro cell found
  by_cases same : source = cell
  · simp [change,same] at found
  · simpa [change,same] using subset cell (by simpa [change,same] using found)

theorem roll_subset_covers (board : Board) (small large holes : Pattern)
    (subset : ∀ cell, small cell = true → large cell = true) (direction : Dir)
    (fuel current : Nat) (result : Ending)
    (checked : rollOracle board large holes direction fuel current = some result) :
    rollOracle board small holes direction fuel current = some result := by
  induction fuel generalizing current with
  | zero => simp [rollOracle] at checked
  | succ fuel ih =>
    cases adjacent : advance board current direction with
    | none => simpa [rollOracle,adjacent] using checked
    | some next =>
      cases door : board.doors.contains next <;>
        cases floor : board.floor.contains next <;>
        cases box : large next <;> cases hole : holes next <;>
        simp only [rollOracle,adjacent,door,floor,box,hole,
          Bool.not_true,Bool.not_false,Bool.false_eq_true,↓reduceIte] at checked ⊢
      all_goals first
        | contradiction
        | exact checked
        | (have smallClear := clear_of_subset small large subset next box
           simp only [smallClear,Bool.false_eq_true,↓reduceIte]
           first | exact checked | exact ih next checked)

theorem push_subset_covers (board : Board) (small large holes : Pattern)
    (subset : ∀ cell, small cell = true → large cell = true) (source : Cell)
    (direction : Dir) (result : Ending)
    (checked : pushOracle board large holes source direction = some result) :
    pushOracle board small holes source direction = some result := by
  cases diagonal : direction.diagonal with
  | true => simp [pushOracle,diagonal] at checked
  | false =>
    cases behind : advance board source direction.opposite with
    | none => simp [pushOracle,diagonal,behind] at checked
    | some cell =>
      cases supportFloor : board.floor.contains cell <;>
        cases supportDoor : board.doors.contains cell <;>
        simp only [pushOracle,diagonal,Bool.false_eq_true,↓reduceIte,bind,
          pure,Option.bind_some,behind,supportFloor,supportDoor,
          Bool.not_true,Bool.not_false,Bool.false_or,Bool.true_or] at checked ⊢
      all_goals first | contradiction | skip
      cases destination : advance board source direction with
      | none => simp [destination] at checked
      | some first =>
        cases floor : board.floor.contains first <;>
          cases door : board.doors.contains first <;> cases box : large first <;>
          cases hole : holes first <;> cases rolling : board.rollingTraps.contains first <;>
          simp only [destination,Option.bind_some,floor,door,box,hole,rolling,
            Bool.not_true,Bool.not_false,Bool.false_or,
            Bool.true_or,Bool.false_eq_true,↓reduceIte] at checked ⊢
        all_goals first
          | contradiction
          | exact checked
          | (have smallClear := clear_of_subset small large subset first box
             simp only [smallClear,Bool.false_or,Bool.false_eq_true,↓reduceIte]
             first
               | exact checked
               | exact roll_subset_covers board _ _ holes (erase_subset small large subset source)
                   direction _ source result checked)

theorem project_subset (selected actual : List Cell) (subset : selected ⊆ actual) :
    ∀ cell, project selected cell = true → project actual cell = true := by
  intro cell present
  exact List.contains_iff_mem.mpr (subset (List.contains_iff_mem.mp present))

/-- Concrete coupling to Model: not a changed rolling rule or an assumed
proposer graph edge. This applies to every selected persistent group. -/
theorem original_push_projected (board : Board) (state : State)
    (selected : List Cell) (subset : selected ⊆ state.boulders)
    (unique : state.boulders.Nodup) (source : Cell) (direction : Dir) (result : PushResult)
    (checked : pushBoulder board state source direction = some result) :
    pushOracle board (project selected) (project state.holes) source direction = some (ending result) := by
  have exactOracle := pushOracle_exact board state unique source direction
  rw [checked,Option.map_some] at exactOracle
  exact push_subset_covers board _ _ _ (project_subset selected state.boulders subset)
    source direction (ending result) exactOracle.symm

theorem original_corner_projected (board : Board) (state : State) (selected : List Cell)
    (subset : selected ⊆ state.boulders) (direction : Dir) (t : Transition)
    (checked : step board state direction = some t) :
    corner board (project selected) state.player direction = false :=
  HeroPhasePotential.corner_clear_mono board _ _ (project_subset selected state.boulders subset)
    state.player direction ((corner_project board state direction).trans
      (FiniteTopology.step_corner_clear board state direction t checked))

end NetHack.Sokoban.GhostProjection
