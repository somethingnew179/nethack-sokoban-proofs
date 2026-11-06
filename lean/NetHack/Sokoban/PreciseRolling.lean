/- A stronger certificate reduction for the unchanged rolling/no-collision
Model. Non-consuming rolls cannot stop at arbitrary ray prefixes. -/
import NetHack.Sokoban.Model
namespace NetHack.Sokoban.PreciseRolling

theorem roll_no_fill_empty (board : Board) (stationary holes : List Cell) (direction : Dir)
    (fuel current : Nat) (result : PushResult)
    (checked : roll board stationary holes direction fuel current = some result)
    (unfilled : result.filled = none) :
    roll board [] [] direction fuel current = some ⟨[result.landing], none, result.landing⟩ := by
  induction fuel generalizing current result with
  | zero => simp [roll] at checked
  | succ fuel ih =>
    cases adjacent : advance board current direction with
    | none =>
      simp [roll, adjacent] at checked
      subst result
      simp [roll, adjacent]
    | some next =>
      by_cases door : next ∈ board.doors
      · simp [roll, adjacent, door] at checked
      · by_cases floor : next ∈ board.floor
        · by_cases collision : next ∈ stationary
          · simp [roll, adjacent, door, floor, collision] at checked
          · by_cases hazard : next ∈ holes
            · simp [roll, adjacent, door, floor, collision, hazard] at checked
              subst result
              cases unfilled
            · simp [roll, adjacent, door, floor, collision, hazard] at checked
              simpa [roll, adjacent, door, floor] using ih next result checked unfilled
        · simp [roll, adjacent, door, floor] at checked
          subst result
          simp [roll, adjacent, door, floor]

/-- Consumption remains covered by rayTargets. Only non-consuming landings
use this stronger set; no change to the executable Model is made. -/
def stayTargets (board : Board) (source : Cell) (direction : Dir) : List Cell :=
  match advance board source direction with
  | none => []
  | some destination =>
    if board.rollingTraps.contains destination then
      match roll board [] [] direction (board.width * board.height + 1) source with
      | none => []
      | some result => [result.landing]
    else [destination]

theorem push_no_fill_target (board : Board) (state : State) (source : Cell)
    (direction : Dir) (result : PushResult)
    (checked : pushBoulder board state source direction = some result)
    (unfilled : result.filled = none) : result.landing ∈ stayTargets board source direction := by
  cases diagonal : direction.diagonal with
  | true => simp [pushBoulder, diagonal] at checked
  | false =>
    cases support : advance board source direction.opposite with
    | none => simp [pushBoulder, diagonal, support] at checked
    | some behind =>
      by_cases behindFloor : behind ∈ board.floor
      · by_cases behindDoor : behind ∈ board.doors
        · simp [pushBoulder, diagonal, support, behindFloor, behindDoor] at checked
        · cases adjacent : advance board source direction with
          | none => simp [pushBoulder, diagonal, support, behindFloor, behindDoor, adjacent] at checked
          | some destination =>
            by_cases floor : destination ∈ board.floor
            · by_cases door : destination ∈ board.doors
              · simp [pushBoulder, diagonal, support, behindFloor, behindDoor, adjacent, floor, door] at checked
              · by_cases collision : destination ∈ state.boulders
                · simp [pushBoulder, diagonal, support, behindFloor, behindDoor, adjacent, floor, door, collision] at checked
                · by_cases hazard : destination ∈ state.holes
                  · simp [pushBoulder, diagonal, support, behindFloor, behindDoor, adjacent, floor, door, collision, hazard] at checked
                    subst result
                    cases unfilled
                  · by_cases rolling : destination ∈ board.rollingTraps
                    · simp [pushBoulder, diagonal, support, behindFloor, behindDoor, adjacent, floor, door, collision, hazard, rolling] at checked
                      have empty := roll_no_fill_empty board (state.boulders.erase source) state.holes direction
                        (board.width * board.height + 1) source result checked unfilled
                      simp [stayTargets, adjacent, rolling, empty]
                    · simp [pushBoulder, diagonal, support, behindFloor, behindDoor, adjacent, floor, door, collision, hazard, rolling] at checked
                      subst result
                      simp [stayTargets, adjacent, rolling]
            · simp [pushBoulder, diagonal, support, behindFloor, behindDoor, adjacent, floor] at checked
      · simp [pushBoulder, diagonal, support, behindFloor] at checked

end NetHack.Sokoban.PreciseRolling
