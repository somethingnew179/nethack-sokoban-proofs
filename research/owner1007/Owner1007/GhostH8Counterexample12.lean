import Owner1007.TokenPartitions
import NetHack.Sokoban.Generated.Soko12Potential
namespace Owner1007.GhostH8Counterexample12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open Owner1007 Owner1007.TokenAccounting
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
/-- Custom eight-token diagnostic only. This is not the original canonical state. -/
def initial : State := {player:=265,boulders:=[108,158,159,186,187,212,237,238],holes:=soko1_2.initial.holes}
def path : List Dir := [.west,.west,.north,.southEast,.northEast,.west,.southWest,.northWest,.north,.north,.north,.east,.northEast,.north,.north,.north,.northWest,.east,.south,.south,.south,.south,.southEast,.south,.west,.north,.north,.north,.north,.north,.northWest,.east,.south,.south,.south,.southWest,.southWest,.northWest,.east,.east,.southEast,.north,.north,.north,.north,.northWest,.east,.south,.south,.south,.south,.southWest,.southWest,.south,.south,.southEast,.northEast,.north,.north,.north,.north,.north,.north,.north,.northWest,.east,.south,.south,.south,.south,.southWest,.southWest,.south,.east,.southWest,.southEast,.northEast,.north,.north,.north,.north,.north,.north,.north,.northWest,.east,.south,.south,.south,.south,.south,.south,.southWest,.north,.north,.northWest,.east,.southEast,.north,.north,.north,.north,.northWest,.east,.south,.south,.south,.south,.south,.south,.south,.south,.south,.southEast,.southEast,.southEast,.southEast,.east,.northEast,.north,.north,.north,.north,.north,.northWest,.west,.west,.southWest,.west,.southWest,.north,.north,.north,.north,.north,.north,.north,.northWest,.east,.south,.south,.south,.south,.south,.south,.south,.south,.southWest,.north,.north,.north,.north,.northWest,.east,.southEast,.north,.north,.north,.north,.northWest,.east]
def result : RunResult := {state:={player:=30,boulders:=[],holes:=[40,41,42,43,44,45,46,47,48,49]},pushes:=67,moves:=161}
theorem checked : run soko1_2.board initial path=some result := by decide +kernel
theorem trace : Trace soko1_2.board initial path result.state 67 161 := run_sound _ _ _ _ checked
theorem remaining_holes : result.state.holes.length=10 := rfl
theorem energy_four : ∃ outcomes,
 Logged soko1_2.board initial path result.state 67 161 outcomes ∧
 energy Generated.soko1_2Potential initial.boulders outcomes=4 := by
 obtain ⟨outcomes,logged⟩:=log_exists trace (by decide +kernel)
 have total:=logged.all_energy Generated.soko1_2Potential
 have start:Generated.soko1_2Potential.value initial=243:=by decide +kernel
 have finish:weightSum Generated.soko1_2Potential.hole result.state.holes=180:=by decide +kernel
 rw[start,finish] at total
 change 243+energy Generated.soko1_2Potential initial.boulders outcomes=(67:Int)+180 at total
 exact ⟨outcomes,logged,by omega⟩
#print axioms trace
#print axioms energy_four
end Owner1007.GhostH8Counterexample12
