/- Transfer between hole configurations, proved for the same endpoint oracle.
No shortest-path or reachable-region quotient is assumed. -/
import NetHack.Sokoban.GhostProjection
namespace NetHack.Sokoban.GhostHoleTransfer
open HazardPattern PatternCorrection
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

theorem push_no_roll_equal (board : Board) (boxes first second : Pattern)
    (source : Cell) (direction : Dir)
    (simple : ∀ destination, advance board source direction = some destination →
      first destination = false ∧ second destination = false ∧
        board.rollingTraps.contains destination = false) :
    pushOracle board boxes first source direction = pushOracle board boxes second source direction := by
  cases diagonal : direction.diagonal with
  | true => simp [pushOracle,diagonal]
  | false =>
    cases behind : advance board source direction.opposite with
    | none => simp [pushOracle,diagonal,behind]
    | some cell =>
      simp only [pushOracle,diagonal,Bool.false_eq_true,↓reduceIte,bind,pure,Option.bind_some,behind]
      split
      · rfl
      · cases destination : advance board source direction with
        | none => simp [destination]
        | some target =>
          rcases simple target destination with ⟨a,b,c⟩
          have notRolling : target ∉ board.rollingTraps := by simpa using c
          simp [destination,a,b,notRolling]

def canonicalEnding (hole : Cell) : Ending → Ending
  | .stay landing => .stay landing
  | .fill _ => .fill hole
def canonicalOutcome (hole : Cell) : Outcome → Outcome
  | .walk target => .walk target
  | .push source ending => .push source (canonicalEnding hole ending)

theorem step_transfer (board : Board) (boxes first second : Pattern)
    (hole hero : Cell) (direction : Dir) (outcome : Outcome)
    (heroClear : first hero = false) (heroClearSecond : second hero = false)
    (subset : ∀ cell, second cell = true → first cell = true)
    (pushes : ∀ source, boxes source = true → ∀ ending,
      pushOracle board boxes first source direction = some ending →
      pushOracle board boxes second source direction = some (canonicalEnding hole ending))
    (oracle : stepOracle board boxes first hero direction = some outcome) :
    stepOracle board boxes second hero direction = some (canonicalOutcome hole outcome) := by
  cases occupied : boxes hero with
  | true => simp [stepOracle,occupied] at oracle
  | false =>
    cases target : advance board hero direction with
    | none => simp [stepOracle,occupied,heroClear,target] at oracle
    | some cell =>
      simp only [stepOracle,occupied,heroClear,heroClearSecond,Bool.false_or,Bool.false_eq_true,
        ↓reduceIte,bind,pure,Option.bind_some,target] at oracle ⊢
      split at oracle
      · contradiction
      · rename_i physical
        rw [if_neg physical]
        cases box : boxes cell with
        | false =>
          cases hazard : first cell with
          | true => simp [box,hazard] at oracle
          | false =>
            have clearSecond := GhostProjection.clear_of_subset second first subset cell hazard
            simp only [box,hazard,clearSecond,Bool.false_eq_true,↓reduceIte] at oracle ⊢
            cases oracle
            rfl
        | true =>
          cases pushed : pushOracle board boxes first cell direction with
          | none => simp [box,pushed] at oracle
          | some result =>
            simp only [box,Bool.true_eq_false,↓reduceIte,pushed,Option.bind_some,Option.some.injEq] at oracle
            subst outcome
            have after := pushes cell box result pushed
            simp [box,after,canonicalOutcome]

end NetHack.Sokoban.GhostHoleTransfer
