import Owner1007.TokenPartitions
import NetHack.Sokoban.Generated.Soko12Potential
namespace Owner1007.GhostUpperCounterexample12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open Owner1007 Owner1007.TokenAccounting
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
/-- A six-token diagnostic relaxation on the original board and transition rules. -/
def initial : State := {player:=187,boulders:=[108,158,159,161,186,212],holes:=soko1_2.initial.holes}
def path : List Dir := [.west,.north,.north,.north,.north,.north,.northWest,.east,.south,.south,.south,.south,.south,.south,.southEast,.southWest,.north,.north,.north,.north,.north,.north,.north,.northWest,.east,.south,.south,.south,.south,.south,.south,.southWest,.northWest,.east,.southEast,.north,.north,.north,.north,.north,.north,.northWest,.east,.south,.south,.south,.south,.south,.southWest,.west,.north,.northWest,.east,.east,.southWest,.southEast,.northEast,.north,.north,.north,.north,.northWest,.east,.south,.south,.south,.south,.south,.southWest,.north,.northWest,.east,.southEast,.north,.north,.north,.north,.northWest,.east,.south,.south,.south,.southEast,.south,.south,.southWest,.south,.south,.southEast,.southEast,.southEast,.southEast,.east,.northEast,.north,.north,.north,.north,.north,.northWest,.west,.west,.southWest,.west,.southWest,.north,.north,.north,.north,.north,.north,.north,.northWest,.east]
def result : RunResult := {state:={player:=30,boulders:=[],holes:=[38,39,40,41,42,43,44,45,46,47,48,49]},pushes:=47,moves:=114}
theorem checked : run soko1_2.board initial path=some result := by decide +kernel
theorem trace : Trace soko1_2.board initial path result.state 47 114 :=
  run_sound _ _ _ _ checked
theorem remaining_holes : result.state.holes.length=12 := rfl

/-- All six marked stones disappear for two units of scalar owned energy.
This refutes the stronger isolated-Upper hypothesis used in diagnostics. -/
theorem energy_two : ∃ outcomes,
    Logged soko1_2.board initial path result.state 47 114 outcomes ∧
    energy Generated.soko1_2Potential initial.boulders outcomes=2 := by
  obtain ⟨outcomes,logged⟩ := log_exists trace (by decide +kernel)
  have total := logged.all_energy Generated.soko1_2Potential
  have start : Generated.soko1_2Potential.value initial=261 := by decide +kernel
  have finish : weightSum Generated.soko1_2Potential.hole result.state.holes=216 := by decide +kernel
  rw [start,finish] at total
  change 261 + energy Generated.soko1_2Potential initial.boulders outcomes = (47 : Int) + 216 at total
  exact ⟨outcomes,logged,by omega⟩
#print axioms trace
#print axioms energy_two
end Owner1007.GhostUpperCounterexample12
