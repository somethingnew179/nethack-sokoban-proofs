import NetHack.Soko12Forward220.Unified.P01.OracleCells10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P01
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem floorAt440 : soko1_2.board.floor.contains 440 = false := by decide +kernel
theorem doorAt440 : soko1_2.board.doors.contains 440 = false := by decide +kernel
theorem trapAt440 : soko1_2.board.rollingTraps.contains 440 = false := by decide +kernel
theorem boxAt440 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p 440 = false := rfl
theorem holeAt440 (p : Pattern) : project (soko1_2.initial.holes.drop 1) 440 = false := rfl
theorem advanceAt440_north : advance soko1_2.board 440 .north = some 414 := by decide +kernel
theorem advanceAt440_south : advance soko1_2.board 440 .south = none := by decide +kernel
theorem advanceAt440_east : advance soko1_2.board 440 .east = some 441 := by decide +kernel
theorem advanceAt440_west : advance soko1_2.board 440 .west = some 439 := by decide +kernel
theorem advanceAt440_northEast : advance soko1_2.board 440 .northEast = some 415 := by decide +kernel
theorem advanceAt440_northWest : advance soko1_2.board 440 .northWest = some 413 := by decide +kernel
theorem advanceAt440_southEast : advance soko1_2.board 440 .southEast = none := by decide +kernel
theorem advanceAt440_southWest : advance soko1_2.board 440 .southWest = none := by decide +kernel
theorem floorAt441 : soko1_2.board.floor.contains 441 = false := by decide +kernel
theorem doorAt441 : soko1_2.board.doors.contains 441 = false := by decide +kernel
theorem trapAt441 : soko1_2.board.rollingTraps.contains 441 = false := by decide +kernel
theorem boxAt441 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p 441 = false := rfl
theorem holeAt441 (p : Pattern) : project (soko1_2.initial.holes.drop 1) 441 = false := rfl
theorem advanceAt441_north : advance soko1_2.board 441 .north = some 415 := by decide +kernel
theorem advanceAt441_south : advance soko1_2.board 441 .south = none := by decide +kernel
theorem advanceAt441_east : advance soko1_2.board 441 .east = none := by decide +kernel
theorem advanceAt441_west : advance soko1_2.board 441 .west = some 440 := by decide +kernel
theorem advanceAt441_northEast : advance soko1_2.board 441 .northEast = none := by decide +kernel
theorem advanceAt441_northWest : advance soko1_2.board 441 .northWest = some 414 := by decide +kernel
theorem advanceAt441_southEast : advance soko1_2.board 441 .southEast = none := by decide +kernel
theorem advanceAt441_southWest : advance soko1_2.board 441 .southWest = none := by decide +kernel
end NetHack.Soko12Forward220.Unified.P01
