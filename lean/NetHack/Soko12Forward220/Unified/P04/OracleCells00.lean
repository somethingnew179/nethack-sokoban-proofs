import NetHack.Soko12Forward220.Unified.P04.OracleBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P04
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem floorAt0 : soko1_2.board.floor.contains 0 = false := by decide +kernel
theorem doorAt0 : soko1_2.board.doors.contains 0 = false := by decide +kernel
theorem trapAt0 : soko1_2.board.rollingTraps.contains 0 = false := by decide +kernel
theorem boxAt0 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 0 = false := rfl
theorem holeAt0 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 0 = false := rfl
theorem advanceAt0_north : advance soko1_2.board 0 .north = none := by decide +kernel
theorem advanceAt0_south : advance soko1_2.board 0 .south = some 26 := by decide +kernel
theorem advanceAt0_east : advance soko1_2.board 0 .east = some 1 := by decide +kernel
theorem advanceAt0_west : advance soko1_2.board 0 .west = none := by decide +kernel
theorem advanceAt0_northEast : advance soko1_2.board 0 .northEast = none := by decide +kernel
theorem advanceAt0_northWest : advance soko1_2.board 0 .northWest = none := by decide +kernel
theorem advanceAt0_southEast : advance soko1_2.board 0 .southEast = some 27 := by decide +kernel
theorem advanceAt0_southWest : advance soko1_2.board 0 .southWest = none := by decide +kernel
theorem floorAt1 : soko1_2.board.floor.contains 1 = false := by decide +kernel
theorem doorAt1 : soko1_2.board.doors.contains 1 = false := by decide +kernel
theorem trapAt1 : soko1_2.board.rollingTraps.contains 1 = false := by decide +kernel
theorem boxAt1 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 1 = false := rfl
theorem holeAt1 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 1 = false := rfl
theorem advanceAt1_north : advance soko1_2.board 1 .north = none := by decide +kernel
theorem advanceAt1_south : advance soko1_2.board 1 .south = some 27 := by decide +kernel
theorem advanceAt1_east : advance soko1_2.board 1 .east = some 2 := by decide +kernel
theorem advanceAt1_west : advance soko1_2.board 1 .west = some 0 := by decide +kernel
theorem advanceAt1_northEast : advance soko1_2.board 1 .northEast = none := by decide +kernel
theorem advanceAt1_northWest : advance soko1_2.board 1 .northWest = none := by decide +kernel
theorem advanceAt1_southEast : advance soko1_2.board 1 .southEast = some 28 := by decide +kernel
theorem advanceAt1_southWest : advance soko1_2.board 1 .southWest = some 26 := by decide +kernel
theorem floorAt2 : soko1_2.board.floor.contains 2 = false := by decide +kernel
theorem doorAt2 : soko1_2.board.doors.contains 2 = false := by decide +kernel
theorem trapAt2 : soko1_2.board.rollingTraps.contains 2 = false := by decide +kernel
theorem boxAt2 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 2 = false := rfl
theorem holeAt2 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 2 = false := rfl
theorem advanceAt2_north : advance soko1_2.board 2 .north = none := by decide +kernel
theorem advanceAt2_south : advance soko1_2.board 2 .south = some 28 := by decide +kernel
theorem advanceAt2_east : advance soko1_2.board 2 .east = some 3 := by decide +kernel
theorem advanceAt2_west : advance soko1_2.board 2 .west = some 1 := by decide +kernel
theorem advanceAt2_northEast : advance soko1_2.board 2 .northEast = none := by decide +kernel
theorem advanceAt2_northWest : advance soko1_2.board 2 .northWest = none := by decide +kernel
theorem advanceAt2_southEast : advance soko1_2.board 2 .southEast = some 29 := by decide +kernel
theorem advanceAt2_southWest : advance soko1_2.board 2 .southWest = some 27 := by decide +kernel
theorem floorAt3 : soko1_2.board.floor.contains 3 = false := by decide +kernel
theorem doorAt3 : soko1_2.board.doors.contains 3 = false := by decide +kernel
theorem trapAt3 : soko1_2.board.rollingTraps.contains 3 = false := by decide +kernel
theorem boxAt3 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 3 = false := rfl
theorem holeAt3 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 3 = false := rfl
theorem advanceAt3_north : advance soko1_2.board 3 .north = none := by decide +kernel
theorem advanceAt3_south : advance soko1_2.board 3 .south = some 29 := by decide +kernel
theorem advanceAt3_east : advance soko1_2.board 3 .east = some 4 := by decide +kernel
theorem advanceAt3_west : advance soko1_2.board 3 .west = some 2 := by decide +kernel
theorem advanceAt3_northEast : advance soko1_2.board 3 .northEast = none := by decide +kernel
theorem advanceAt3_northWest : advance soko1_2.board 3 .northWest = none := by decide +kernel
theorem advanceAt3_southEast : advance soko1_2.board 3 .southEast = some 30 := by decide +kernel
theorem advanceAt3_southWest : advance soko1_2.board 3 .southWest = some 28 := by decide +kernel
theorem floorAt4 : soko1_2.board.floor.contains 4 = false := by decide +kernel
theorem doorAt4 : soko1_2.board.doors.contains 4 = false := by decide +kernel
theorem trapAt4 : soko1_2.board.rollingTraps.contains 4 = false := by decide +kernel
theorem boxAt4 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 4 = false := rfl
theorem holeAt4 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 4 = false := rfl
theorem advanceAt4_north : advance soko1_2.board 4 .north = none := by decide +kernel
theorem advanceAt4_south : advance soko1_2.board 4 .south = some 30 := by decide +kernel
theorem advanceAt4_east : advance soko1_2.board 4 .east = some 5 := by decide +kernel
theorem advanceAt4_west : advance soko1_2.board 4 .west = some 3 := by decide +kernel
theorem advanceAt4_northEast : advance soko1_2.board 4 .northEast = none := by decide +kernel
theorem advanceAt4_northWest : advance soko1_2.board 4 .northWest = none := by decide +kernel
theorem advanceAt4_southEast : advance soko1_2.board 4 .southEast = some 31 := by decide +kernel
theorem advanceAt4_southWest : advance soko1_2.board 4 .southWest = some 29 := by decide +kernel
theorem floorAt5 : soko1_2.board.floor.contains 5 = false := by decide +kernel
theorem doorAt5 : soko1_2.board.doors.contains 5 = false := by decide +kernel
theorem trapAt5 : soko1_2.board.rollingTraps.contains 5 = false := by decide +kernel
theorem boxAt5 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 5 = false := rfl
theorem holeAt5 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 5 = false := rfl
theorem advanceAt5_north : advance soko1_2.board 5 .north = none := by decide +kernel
theorem advanceAt5_south : advance soko1_2.board 5 .south = some 31 := by decide +kernel
theorem advanceAt5_east : advance soko1_2.board 5 .east = some 6 := by decide +kernel
theorem advanceAt5_west : advance soko1_2.board 5 .west = some 4 := by decide +kernel
theorem advanceAt5_northEast : advance soko1_2.board 5 .northEast = none := by decide +kernel
theorem advanceAt5_northWest : advance soko1_2.board 5 .northWest = none := by decide +kernel
theorem advanceAt5_southEast : advance soko1_2.board 5 .southEast = some 32 := by decide +kernel
theorem advanceAt5_southWest : advance soko1_2.board 5 .southWest = some 30 := by decide +kernel
theorem floorAt6 : soko1_2.board.floor.contains 6 = false := by decide +kernel
theorem doorAt6 : soko1_2.board.doors.contains 6 = false := by decide +kernel
theorem trapAt6 : soko1_2.board.rollingTraps.contains 6 = false := by decide +kernel
theorem boxAt6 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 6 = false := rfl
theorem holeAt6 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 6 = false := rfl
theorem advanceAt6_north : advance soko1_2.board 6 .north = none := by decide +kernel
theorem advanceAt6_south : advance soko1_2.board 6 .south = some 32 := by decide +kernel
theorem advanceAt6_east : advance soko1_2.board 6 .east = some 7 := by decide +kernel
theorem advanceAt6_west : advance soko1_2.board 6 .west = some 5 := by decide +kernel
theorem advanceAt6_northEast : advance soko1_2.board 6 .northEast = none := by decide +kernel
theorem advanceAt6_northWest : advance soko1_2.board 6 .northWest = none := by decide +kernel
theorem advanceAt6_southEast : advance soko1_2.board 6 .southEast = some 33 := by decide +kernel
theorem advanceAt6_southWest : advance soko1_2.board 6 .southWest = some 31 := by decide +kernel
theorem floorAt7 : soko1_2.board.floor.contains 7 = false := by decide +kernel
theorem doorAt7 : soko1_2.board.doors.contains 7 = false := by decide +kernel
theorem trapAt7 : soko1_2.board.rollingTraps.contains 7 = false := by decide +kernel
theorem boxAt7 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 7 = false := rfl
theorem holeAt7 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 7 = false := rfl
theorem advanceAt7_north : advance soko1_2.board 7 .north = none := by decide +kernel
theorem advanceAt7_south : advance soko1_2.board 7 .south = some 33 := by decide +kernel
theorem advanceAt7_east : advance soko1_2.board 7 .east = some 8 := by decide +kernel
theorem advanceAt7_west : advance soko1_2.board 7 .west = some 6 := by decide +kernel
theorem advanceAt7_northEast : advance soko1_2.board 7 .northEast = none := by decide +kernel
theorem advanceAt7_northWest : advance soko1_2.board 7 .northWest = none := by decide +kernel
theorem advanceAt7_southEast : advance soko1_2.board 7 .southEast = some 34 := by decide +kernel
theorem advanceAt7_southWest : advance soko1_2.board 7 .southWest = some 32 := by decide +kernel
theorem floorAt8 : soko1_2.board.floor.contains 8 = false := by decide +kernel
theorem doorAt8 : soko1_2.board.doors.contains 8 = false := by decide +kernel
theorem trapAt8 : soko1_2.board.rollingTraps.contains 8 = false := by decide +kernel
theorem boxAt8 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 8 = false := rfl
theorem holeAt8 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 8 = false := rfl
theorem advanceAt8_north : advance soko1_2.board 8 .north = none := by decide +kernel
theorem advanceAt8_south : advance soko1_2.board 8 .south = some 34 := by decide +kernel
theorem advanceAt8_east : advance soko1_2.board 8 .east = some 9 := by decide +kernel
theorem advanceAt8_west : advance soko1_2.board 8 .west = some 7 := by decide +kernel
theorem advanceAt8_northEast : advance soko1_2.board 8 .northEast = none := by decide +kernel
theorem advanceAt8_northWest : advance soko1_2.board 8 .northWest = none := by decide +kernel
theorem advanceAt8_southEast : advance soko1_2.board 8 .southEast = some 35 := by decide +kernel
theorem advanceAt8_southWest : advance soko1_2.board 8 .southWest = some 33 := by decide +kernel
theorem floorAt9 : soko1_2.board.floor.contains 9 = false := by decide +kernel
theorem doorAt9 : soko1_2.board.doors.contains 9 = false := by decide +kernel
theorem trapAt9 : soko1_2.board.rollingTraps.contains 9 = false := by decide +kernel
theorem boxAt9 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 9 = false := rfl
theorem holeAt9 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 9 = false := rfl
theorem advanceAt9_north : advance soko1_2.board 9 .north = none := by decide +kernel
theorem advanceAt9_south : advance soko1_2.board 9 .south = some 35 := by decide +kernel
theorem advanceAt9_east : advance soko1_2.board 9 .east = some 10 := by decide +kernel
theorem advanceAt9_west : advance soko1_2.board 9 .west = some 8 := by decide +kernel
theorem advanceAt9_northEast : advance soko1_2.board 9 .northEast = none := by decide +kernel
theorem advanceAt9_northWest : advance soko1_2.board 9 .northWest = none := by decide +kernel
theorem advanceAt9_southEast : advance soko1_2.board 9 .southEast = some 36 := by decide +kernel
theorem advanceAt9_southWest : advance soko1_2.board 9 .southWest = some 34 := by decide +kernel
theorem floorAt10 : soko1_2.board.floor.contains 10 = false := by decide +kernel
theorem doorAt10 : soko1_2.board.doors.contains 10 = false := by decide +kernel
theorem trapAt10 : soko1_2.board.rollingTraps.contains 10 = false := by decide +kernel
theorem boxAt10 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 10 = false := rfl
theorem holeAt10 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 10 = false := rfl
theorem advanceAt10_north : advance soko1_2.board 10 .north = none := by decide +kernel
theorem advanceAt10_south : advance soko1_2.board 10 .south = some 36 := by decide +kernel
theorem advanceAt10_east : advance soko1_2.board 10 .east = some 11 := by decide +kernel
theorem advanceAt10_west : advance soko1_2.board 10 .west = some 9 := by decide +kernel
theorem advanceAt10_northEast : advance soko1_2.board 10 .northEast = none := by decide +kernel
theorem advanceAt10_northWest : advance soko1_2.board 10 .northWest = none := by decide +kernel
theorem advanceAt10_southEast : advance soko1_2.board 10 .southEast = some 37 := by decide +kernel
theorem advanceAt10_southWest : advance soko1_2.board 10 .southWest = some 35 := by decide +kernel
theorem floorAt11 : soko1_2.board.floor.contains 11 = false := by decide +kernel
theorem doorAt11 : soko1_2.board.doors.contains 11 = false := by decide +kernel
theorem trapAt11 : soko1_2.board.rollingTraps.contains 11 = false := by decide +kernel
theorem boxAt11 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 11 = false := rfl
theorem holeAt11 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 11 = false := rfl
theorem advanceAt11_north : advance soko1_2.board 11 .north = none := by decide +kernel
theorem advanceAt11_south : advance soko1_2.board 11 .south = some 37 := by decide +kernel
theorem advanceAt11_east : advance soko1_2.board 11 .east = some 12 := by decide +kernel
theorem advanceAt11_west : advance soko1_2.board 11 .west = some 10 := by decide +kernel
theorem advanceAt11_northEast : advance soko1_2.board 11 .northEast = none := by decide +kernel
theorem advanceAt11_northWest : advance soko1_2.board 11 .northWest = none := by decide +kernel
theorem advanceAt11_southEast : advance soko1_2.board 11 .southEast = some 38 := by decide +kernel
theorem advanceAt11_southWest : advance soko1_2.board 11 .southWest = some 36 := by decide +kernel
theorem floorAt12 : soko1_2.board.floor.contains 12 = false := by decide +kernel
theorem doorAt12 : soko1_2.board.doors.contains 12 = false := by decide +kernel
theorem trapAt12 : soko1_2.board.rollingTraps.contains 12 = false := by decide +kernel
theorem boxAt12 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 12 = false := rfl
theorem holeAt12 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 12 = false := rfl
theorem advanceAt12_north : advance soko1_2.board 12 .north = none := by decide +kernel
theorem advanceAt12_south : advance soko1_2.board 12 .south = some 38 := by decide +kernel
theorem advanceAt12_east : advance soko1_2.board 12 .east = some 13 := by decide +kernel
theorem advanceAt12_west : advance soko1_2.board 12 .west = some 11 := by decide +kernel
theorem advanceAt12_northEast : advance soko1_2.board 12 .northEast = none := by decide +kernel
theorem advanceAt12_northWest : advance soko1_2.board 12 .northWest = none := by decide +kernel
theorem advanceAt12_southEast : advance soko1_2.board 12 .southEast = some 39 := by decide +kernel
theorem advanceAt12_southWest : advance soko1_2.board 12 .southWest = some 37 := by decide +kernel
theorem floorAt13 : soko1_2.board.floor.contains 13 = false := by decide +kernel
theorem doorAt13 : soko1_2.board.doors.contains 13 = false := by decide +kernel
theorem trapAt13 : soko1_2.board.rollingTraps.contains 13 = false := by decide +kernel
theorem boxAt13 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 13 = false := rfl
theorem holeAt13 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 13 = false := rfl
theorem advanceAt13_north : advance soko1_2.board 13 .north = none := by decide +kernel
theorem advanceAt13_south : advance soko1_2.board 13 .south = some 39 := by decide +kernel
theorem advanceAt13_east : advance soko1_2.board 13 .east = some 14 := by decide +kernel
theorem advanceAt13_west : advance soko1_2.board 13 .west = some 12 := by decide +kernel
theorem advanceAt13_northEast : advance soko1_2.board 13 .northEast = none := by decide +kernel
theorem advanceAt13_northWest : advance soko1_2.board 13 .northWest = none := by decide +kernel
theorem advanceAt13_southEast : advance soko1_2.board 13 .southEast = some 40 := by decide +kernel
theorem advanceAt13_southWest : advance soko1_2.board 13 .southWest = some 38 := by decide +kernel
theorem floorAt14 : soko1_2.board.floor.contains 14 = false := by decide +kernel
theorem doorAt14 : soko1_2.board.doors.contains 14 = false := by decide +kernel
theorem trapAt14 : soko1_2.board.rollingTraps.contains 14 = false := by decide +kernel
theorem boxAt14 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 14 = false := rfl
theorem holeAt14 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 14 = false := rfl
theorem advanceAt14_north : advance soko1_2.board 14 .north = none := by decide +kernel
theorem advanceAt14_south : advance soko1_2.board 14 .south = some 40 := by decide +kernel
theorem advanceAt14_east : advance soko1_2.board 14 .east = some 15 := by decide +kernel
theorem advanceAt14_west : advance soko1_2.board 14 .west = some 13 := by decide +kernel
theorem advanceAt14_northEast : advance soko1_2.board 14 .northEast = none := by decide +kernel
theorem advanceAt14_northWest : advance soko1_2.board 14 .northWest = none := by decide +kernel
theorem advanceAt14_southEast : advance soko1_2.board 14 .southEast = some 41 := by decide +kernel
theorem advanceAt14_southWest : advance soko1_2.board 14 .southWest = some 39 := by decide +kernel
theorem floorAt15 : soko1_2.board.floor.contains 15 = false := by decide +kernel
theorem doorAt15 : soko1_2.board.doors.contains 15 = false := by decide +kernel
theorem trapAt15 : soko1_2.board.rollingTraps.contains 15 = false := by decide +kernel
theorem boxAt15 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 15 = false := rfl
theorem holeAt15 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 15 = false := rfl
theorem advanceAt15_north : advance soko1_2.board 15 .north = none := by decide +kernel
theorem advanceAt15_south : advance soko1_2.board 15 .south = some 41 := by decide +kernel
theorem advanceAt15_east : advance soko1_2.board 15 .east = some 16 := by decide +kernel
theorem advanceAt15_west : advance soko1_2.board 15 .west = some 14 := by decide +kernel
theorem advanceAt15_northEast : advance soko1_2.board 15 .northEast = none := by decide +kernel
theorem advanceAt15_northWest : advance soko1_2.board 15 .northWest = none := by decide +kernel
theorem advanceAt15_southEast : advance soko1_2.board 15 .southEast = some 42 := by decide +kernel
theorem advanceAt15_southWest : advance soko1_2.board 15 .southWest = some 40 := by decide +kernel
theorem floorAt16 : soko1_2.board.floor.contains 16 = false := by decide +kernel
theorem doorAt16 : soko1_2.board.doors.contains 16 = false := by decide +kernel
theorem trapAt16 : soko1_2.board.rollingTraps.contains 16 = false := by decide +kernel
theorem boxAt16 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 16 = false := rfl
theorem holeAt16 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 16 = false := rfl
theorem advanceAt16_north : advance soko1_2.board 16 .north = none := by decide +kernel
theorem advanceAt16_south : advance soko1_2.board 16 .south = some 42 := by decide +kernel
theorem advanceAt16_east : advance soko1_2.board 16 .east = some 17 := by decide +kernel
theorem advanceAt16_west : advance soko1_2.board 16 .west = some 15 := by decide +kernel
theorem advanceAt16_northEast : advance soko1_2.board 16 .northEast = none := by decide +kernel
theorem advanceAt16_northWest : advance soko1_2.board 16 .northWest = none := by decide +kernel
theorem advanceAt16_southEast : advance soko1_2.board 16 .southEast = some 43 := by decide +kernel
theorem advanceAt16_southWest : advance soko1_2.board 16 .southWest = some 41 := by decide +kernel
theorem floorAt17 : soko1_2.board.floor.contains 17 = false := by decide +kernel
theorem doorAt17 : soko1_2.board.doors.contains 17 = false := by decide +kernel
theorem trapAt17 : soko1_2.board.rollingTraps.contains 17 = false := by decide +kernel
theorem boxAt17 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 17 = false := rfl
theorem holeAt17 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 17 = false := rfl
theorem advanceAt17_north : advance soko1_2.board 17 .north = none := by decide +kernel
theorem advanceAt17_south : advance soko1_2.board 17 .south = some 43 := by decide +kernel
theorem advanceAt17_east : advance soko1_2.board 17 .east = some 18 := by decide +kernel
theorem advanceAt17_west : advance soko1_2.board 17 .west = some 16 := by decide +kernel
theorem advanceAt17_northEast : advance soko1_2.board 17 .northEast = none := by decide +kernel
theorem advanceAt17_northWest : advance soko1_2.board 17 .northWest = none := by decide +kernel
theorem advanceAt17_southEast : advance soko1_2.board 17 .southEast = some 44 := by decide +kernel
theorem advanceAt17_southWest : advance soko1_2.board 17 .southWest = some 42 := by decide +kernel
theorem floorAt18 : soko1_2.board.floor.contains 18 = false := by decide +kernel
theorem doorAt18 : soko1_2.board.doors.contains 18 = false := by decide +kernel
theorem trapAt18 : soko1_2.board.rollingTraps.contains 18 = false := by decide +kernel
theorem boxAt18 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 18 = false := rfl
theorem holeAt18 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 18 = false := rfl
theorem advanceAt18_north : advance soko1_2.board 18 .north = none := by decide +kernel
theorem advanceAt18_south : advance soko1_2.board 18 .south = some 44 := by decide +kernel
theorem advanceAt18_east : advance soko1_2.board 18 .east = some 19 := by decide +kernel
theorem advanceAt18_west : advance soko1_2.board 18 .west = some 17 := by decide +kernel
theorem advanceAt18_northEast : advance soko1_2.board 18 .northEast = none := by decide +kernel
theorem advanceAt18_northWest : advance soko1_2.board 18 .northWest = none := by decide +kernel
theorem advanceAt18_southEast : advance soko1_2.board 18 .southEast = some 45 := by decide +kernel
theorem advanceAt18_southWest : advance soko1_2.board 18 .southWest = some 43 := by decide +kernel
theorem floorAt19 : soko1_2.board.floor.contains 19 = false := by decide +kernel
theorem doorAt19 : soko1_2.board.doors.contains 19 = false := by decide +kernel
theorem trapAt19 : soko1_2.board.rollingTraps.contains 19 = false := by decide +kernel
theorem boxAt19 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 19 = false := rfl
theorem holeAt19 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 19 = false := rfl
theorem advanceAt19_north : advance soko1_2.board 19 .north = none := by decide +kernel
theorem advanceAt19_south : advance soko1_2.board 19 .south = some 45 := by decide +kernel
theorem advanceAt19_east : advance soko1_2.board 19 .east = some 20 := by decide +kernel
theorem advanceAt19_west : advance soko1_2.board 19 .west = some 18 := by decide +kernel
theorem advanceAt19_northEast : advance soko1_2.board 19 .northEast = none := by decide +kernel
theorem advanceAt19_northWest : advance soko1_2.board 19 .northWest = none := by decide +kernel
theorem advanceAt19_southEast : advance soko1_2.board 19 .southEast = some 46 := by decide +kernel
theorem advanceAt19_southWest : advance soko1_2.board 19 .southWest = some 44 := by decide +kernel
theorem floorAt20 : soko1_2.board.floor.contains 20 = false := by decide +kernel
theorem doorAt20 : soko1_2.board.doors.contains 20 = false := by decide +kernel
theorem trapAt20 : soko1_2.board.rollingTraps.contains 20 = false := by decide +kernel
theorem boxAt20 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 20 = false := rfl
theorem holeAt20 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 20 = false := rfl
theorem advanceAt20_north : advance soko1_2.board 20 .north = none := by decide +kernel
theorem advanceAt20_south : advance soko1_2.board 20 .south = some 46 := by decide +kernel
theorem advanceAt20_east : advance soko1_2.board 20 .east = some 21 := by decide +kernel
theorem advanceAt20_west : advance soko1_2.board 20 .west = some 19 := by decide +kernel
theorem advanceAt20_northEast : advance soko1_2.board 20 .northEast = none := by decide +kernel
theorem advanceAt20_northWest : advance soko1_2.board 20 .northWest = none := by decide +kernel
theorem advanceAt20_southEast : advance soko1_2.board 20 .southEast = some 47 := by decide +kernel
theorem advanceAt20_southWest : advance soko1_2.board 20 .southWest = some 45 := by decide +kernel
theorem floorAt21 : soko1_2.board.floor.contains 21 = false := by decide +kernel
theorem doorAt21 : soko1_2.board.doors.contains 21 = false := by decide +kernel
theorem trapAt21 : soko1_2.board.rollingTraps.contains 21 = false := by decide +kernel
theorem boxAt21 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 21 = false := rfl
theorem holeAt21 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 21 = false := rfl
theorem advanceAt21_north : advance soko1_2.board 21 .north = none := by decide +kernel
theorem advanceAt21_south : advance soko1_2.board 21 .south = some 47 := by decide +kernel
theorem advanceAt21_east : advance soko1_2.board 21 .east = some 22 := by decide +kernel
theorem advanceAt21_west : advance soko1_2.board 21 .west = some 20 := by decide +kernel
theorem advanceAt21_northEast : advance soko1_2.board 21 .northEast = none := by decide +kernel
theorem advanceAt21_northWest : advance soko1_2.board 21 .northWest = none := by decide +kernel
theorem advanceAt21_southEast : advance soko1_2.board 21 .southEast = some 48 := by decide +kernel
theorem advanceAt21_southWest : advance soko1_2.board 21 .southWest = some 46 := by decide +kernel
theorem floorAt22 : soko1_2.board.floor.contains 22 = false := by decide +kernel
theorem doorAt22 : soko1_2.board.doors.contains 22 = false := by decide +kernel
theorem trapAt22 : soko1_2.board.rollingTraps.contains 22 = false := by decide +kernel
theorem boxAt22 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 22 = false := rfl
theorem holeAt22 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 22 = false := rfl
theorem advanceAt22_north : advance soko1_2.board 22 .north = none := by decide +kernel
theorem advanceAt22_south : advance soko1_2.board 22 .south = some 48 := by decide +kernel
theorem advanceAt22_east : advance soko1_2.board 22 .east = some 23 := by decide +kernel
theorem advanceAt22_west : advance soko1_2.board 22 .west = some 21 := by decide +kernel
theorem advanceAt22_northEast : advance soko1_2.board 22 .northEast = none := by decide +kernel
theorem advanceAt22_northWest : advance soko1_2.board 22 .northWest = none := by decide +kernel
theorem advanceAt22_southEast : advance soko1_2.board 22 .southEast = some 49 := by decide +kernel
theorem advanceAt22_southWest : advance soko1_2.board 22 .southWest = some 47 := by decide +kernel
theorem floorAt23 : soko1_2.board.floor.contains 23 = false := by decide +kernel
theorem doorAt23 : soko1_2.board.doors.contains 23 = false := by decide +kernel
theorem trapAt23 : soko1_2.board.rollingTraps.contains 23 = false := by decide +kernel
theorem boxAt23 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 23 = false := rfl
theorem holeAt23 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 23 = false := rfl
theorem advanceAt23_north : advance soko1_2.board 23 .north = none := by decide +kernel
theorem advanceAt23_south : advance soko1_2.board 23 .south = some 49 := by decide +kernel
theorem advanceAt23_east : advance soko1_2.board 23 .east = some 24 := by decide +kernel
theorem advanceAt23_west : advance soko1_2.board 23 .west = some 22 := by decide +kernel
theorem advanceAt23_northEast : advance soko1_2.board 23 .northEast = none := by decide +kernel
theorem advanceAt23_northWest : advance soko1_2.board 23 .northWest = none := by decide +kernel
theorem advanceAt23_southEast : advance soko1_2.board 23 .southEast = some 50 := by decide +kernel
theorem advanceAt23_southWest : advance soko1_2.board 23 .southWest = some 48 := by decide +kernel
theorem floorAt24 : soko1_2.board.floor.contains 24 = false := by decide +kernel
theorem doorAt24 : soko1_2.board.doors.contains 24 = false := by decide +kernel
theorem trapAt24 : soko1_2.board.rollingTraps.contains 24 = false := by decide +kernel
theorem boxAt24 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 24 = false := rfl
theorem holeAt24 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 24 = false := rfl
theorem advanceAt24_north : advance soko1_2.board 24 .north = none := by decide +kernel
theorem advanceAt24_south : advance soko1_2.board 24 .south = some 50 := by decide +kernel
theorem advanceAt24_east : advance soko1_2.board 24 .east = some 25 := by decide +kernel
theorem advanceAt24_west : advance soko1_2.board 24 .west = some 23 := by decide +kernel
theorem advanceAt24_northEast : advance soko1_2.board 24 .northEast = none := by decide +kernel
theorem advanceAt24_northWest : advance soko1_2.board 24 .northWest = none := by decide +kernel
theorem advanceAt24_southEast : advance soko1_2.board 24 .southEast = some 51 := by decide +kernel
theorem advanceAt24_southWest : advance soko1_2.board 24 .southWest = some 49 := by decide +kernel
theorem floorAt25 : soko1_2.board.floor.contains 25 = false := by decide +kernel
theorem doorAt25 : soko1_2.board.doors.contains 25 = false := by decide +kernel
theorem trapAt25 : soko1_2.board.rollingTraps.contains 25 = false := by decide +kernel
theorem boxAt25 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 25 = false := rfl
theorem holeAt25 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 25 = false := rfl
theorem advanceAt25_north : advance soko1_2.board 25 .north = none := by decide +kernel
theorem advanceAt25_south : advance soko1_2.board 25 .south = some 51 := by decide +kernel
theorem advanceAt25_east : advance soko1_2.board 25 .east = none := by decide +kernel
theorem advanceAt25_west : advance soko1_2.board 25 .west = some 24 := by decide +kernel
theorem advanceAt25_northEast : advance soko1_2.board 25 .northEast = none := by decide +kernel
theorem advanceAt25_northWest : advance soko1_2.board 25 .northWest = none := by decide +kernel
theorem advanceAt25_southEast : advance soko1_2.board 25 .southEast = none := by decide +kernel
theorem advanceAt25_southWest : advance soko1_2.board 25 .southWest = some 50 := by decide +kernel
theorem floorAt26 : soko1_2.board.floor.contains 26 = false := by decide +kernel
theorem doorAt26 : soko1_2.board.doors.contains 26 = false := by decide +kernel
theorem trapAt26 : soko1_2.board.rollingTraps.contains 26 = false := by decide +kernel
theorem boxAt26 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 26 = false := rfl
theorem holeAt26 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 26 = false := rfl
theorem advanceAt26_north : advance soko1_2.board 26 .north = some 0 := by decide +kernel
theorem advanceAt26_south : advance soko1_2.board 26 .south = some 52 := by decide +kernel
theorem advanceAt26_east : advance soko1_2.board 26 .east = some 27 := by decide +kernel
theorem advanceAt26_west : advance soko1_2.board 26 .west = none := by decide +kernel
theorem advanceAt26_northEast : advance soko1_2.board 26 .northEast = some 1 := by decide +kernel
theorem advanceAt26_northWest : advance soko1_2.board 26 .northWest = none := by decide +kernel
theorem advanceAt26_southEast : advance soko1_2.board 26 .southEast = some 53 := by decide +kernel
theorem advanceAt26_southWest : advance soko1_2.board 26 .southWest = none := by decide +kernel
theorem floorAt27 : soko1_2.board.floor.contains 27 = false := by decide +kernel
theorem doorAt27 : soko1_2.board.doors.contains 27 = false := by decide +kernel
theorem trapAt27 : soko1_2.board.rollingTraps.contains 27 = false := by decide +kernel
theorem boxAt27 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 27 = false := rfl
theorem holeAt27 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 27 = false := rfl
theorem advanceAt27_north : advance soko1_2.board 27 .north = some 1 := by decide +kernel
theorem advanceAt27_south : advance soko1_2.board 27 .south = some 53 := by decide +kernel
theorem advanceAt27_east : advance soko1_2.board 27 .east = some 28 := by decide +kernel
theorem advanceAt27_west : advance soko1_2.board 27 .west = some 26 := by decide +kernel
theorem advanceAt27_northEast : advance soko1_2.board 27 .northEast = some 2 := by decide +kernel
theorem advanceAt27_northWest : advance soko1_2.board 27 .northWest = some 0 := by decide +kernel
theorem advanceAt27_southEast : advance soko1_2.board 27 .southEast = some 54 := by decide +kernel
theorem advanceAt27_southWest : advance soko1_2.board 27 .southWest = some 52 := by decide +kernel
theorem floorAt28 : soko1_2.board.floor.contains 28 = false := by decide +kernel
theorem doorAt28 : soko1_2.board.doors.contains 28 = false := by decide +kernel
theorem trapAt28 : soko1_2.board.rollingTraps.contains 28 = false := by decide +kernel
theorem boxAt28 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 28 = false := rfl
theorem holeAt28 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 28 = false := rfl
theorem advanceAt28_north : advance soko1_2.board 28 .north = some 2 := by decide +kernel
theorem advanceAt28_south : advance soko1_2.board 28 .south = some 54 := by decide +kernel
theorem advanceAt28_east : advance soko1_2.board 28 .east = some 29 := by decide +kernel
theorem advanceAt28_west : advance soko1_2.board 28 .west = some 27 := by decide +kernel
theorem advanceAt28_northEast : advance soko1_2.board 28 .northEast = some 3 := by decide +kernel
theorem advanceAt28_northWest : advance soko1_2.board 28 .northWest = some 1 := by decide +kernel
theorem advanceAt28_southEast : advance soko1_2.board 28 .southEast = some 55 := by decide +kernel
theorem advanceAt28_southWest : advance soko1_2.board 28 .southWest = some 53 := by decide +kernel
theorem floorAt29 : soko1_2.board.floor.contains 29 = true := by decide +kernel
theorem doorAt29 : soko1_2.board.doors.contains 29 = false := by decide +kernel
theorem trapAt29 : soko1_2.board.rollingTraps.contains 29 = false := by decide +kernel
theorem boxAt29 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 29 = p 29 := rfl
theorem holeAt29 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 29 = false := rfl
theorem advanceAt29_north : advance soko1_2.board 29 .north = some 3 := by decide +kernel
theorem advanceAt29_south : advance soko1_2.board 29 .south = some 55 := by decide +kernel
theorem advanceAt29_east : advance soko1_2.board 29 .east = some 30 := by decide +kernel
theorem advanceAt29_west : advance soko1_2.board 29 .west = some 28 := by decide +kernel
theorem advanceAt29_northEast : advance soko1_2.board 29 .northEast = some 4 := by decide +kernel
theorem advanceAt29_northWest : advance soko1_2.board 29 .northWest = some 2 := by decide +kernel
theorem advanceAt29_southEast : advance soko1_2.board 29 .southEast = some 56 := by decide +kernel
theorem advanceAt29_southWest : advance soko1_2.board 29 .southWest = some 54 := by decide +kernel
theorem floorAt30 : soko1_2.board.floor.contains 30 = true := by decide +kernel
theorem doorAt30 : soko1_2.board.doors.contains 30 = false := by decide +kernel
theorem trapAt30 : soko1_2.board.rollingTraps.contains 30 = false := by decide +kernel
theorem boxAt30 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 30 = p 30 := rfl
theorem holeAt30 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 30 = false := rfl
theorem advanceAt30_north : advance soko1_2.board 30 .north = some 4 := by decide +kernel
theorem advanceAt30_south : advance soko1_2.board 30 .south = some 56 := by decide +kernel
theorem advanceAt30_east : advance soko1_2.board 30 .east = some 31 := by decide +kernel
theorem advanceAt30_west : advance soko1_2.board 30 .west = some 29 := by decide +kernel
theorem advanceAt30_northEast : advance soko1_2.board 30 .northEast = some 5 := by decide +kernel
theorem advanceAt30_northWest : advance soko1_2.board 30 .northWest = some 3 := by decide +kernel
theorem advanceAt30_southEast : advance soko1_2.board 30 .southEast = some 57 := by decide +kernel
theorem advanceAt30_southWest : advance soko1_2.board 30 .southWest = some 55 := by decide +kernel
theorem floorAt31 : soko1_2.board.floor.contains 31 = true := by decide +kernel
theorem doorAt31 : soko1_2.board.doors.contains 31 = false := by decide +kernel
theorem trapAt31 : soko1_2.board.rollingTraps.contains 31 = true := by decide +kernel
theorem boxAt31 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 31 = false := rfl
theorem holeAt31 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 31 = false := rfl
theorem advanceAt31_north : advance soko1_2.board 31 .north = some 5 := by decide +kernel
theorem advanceAt31_south : advance soko1_2.board 31 .south = some 57 := by decide +kernel
theorem advanceAt31_east : advance soko1_2.board 31 .east = some 32 := by decide +kernel
theorem advanceAt31_west : advance soko1_2.board 31 .west = some 30 := by decide +kernel
theorem advanceAt31_northEast : advance soko1_2.board 31 .northEast = some 6 := by decide +kernel
theorem advanceAt31_northWest : advance soko1_2.board 31 .northWest = some 4 := by decide +kernel
theorem advanceAt31_southEast : advance soko1_2.board 31 .southEast = some 58 := by decide +kernel
theorem advanceAt31_southWest : advance soko1_2.board 31 .southWest = some 56 := by decide +kernel
theorem floorAt32 : soko1_2.board.floor.contains 32 = true := by decide +kernel
theorem doorAt32 : soko1_2.board.doors.contains 32 = false := by decide +kernel
theorem trapAt32 : soko1_2.board.rollingTraps.contains 32 = false := by decide +kernel
theorem boxAt32 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 32 = false := rfl
theorem holeAt32 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 32 = false := rfl
theorem advanceAt32_north : advance soko1_2.board 32 .north = some 6 := by decide +kernel
theorem advanceAt32_south : advance soko1_2.board 32 .south = some 58 := by decide +kernel
theorem advanceAt32_east : advance soko1_2.board 32 .east = some 33 := by decide +kernel
theorem advanceAt32_west : advance soko1_2.board 32 .west = some 31 := by decide +kernel
theorem advanceAt32_northEast : advance soko1_2.board 32 .northEast = some 7 := by decide +kernel
theorem advanceAt32_northWest : advance soko1_2.board 32 .northWest = some 5 := by decide +kernel
theorem advanceAt32_southEast : advance soko1_2.board 32 .southEast = some 59 := by decide +kernel
theorem advanceAt32_southWest : advance soko1_2.board 32 .southWest = some 57 := by decide +kernel
theorem floorAt33 : soko1_2.board.floor.contains 33 = true := by decide +kernel
theorem doorAt33 : soko1_2.board.doors.contains 33 = false := by decide +kernel
theorem trapAt33 : soko1_2.board.rollingTraps.contains 33 = false := by decide +kernel
theorem boxAt33 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 33 = false := rfl
theorem holeAt33 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 33 = false := rfl
theorem advanceAt33_north : advance soko1_2.board 33 .north = some 7 := by decide +kernel
theorem advanceAt33_south : advance soko1_2.board 33 .south = some 59 := by decide +kernel
theorem advanceAt33_east : advance soko1_2.board 33 .east = some 34 := by decide +kernel
theorem advanceAt33_west : advance soko1_2.board 33 .west = some 32 := by decide +kernel
theorem advanceAt33_northEast : advance soko1_2.board 33 .northEast = some 8 := by decide +kernel
theorem advanceAt33_northWest : advance soko1_2.board 33 .northWest = some 6 := by decide +kernel
theorem advanceAt33_southEast : advance soko1_2.board 33 .southEast = some 60 := by decide +kernel
theorem advanceAt33_southWest : advance soko1_2.board 33 .southWest = some 58 := by decide +kernel
theorem floorAt34 : soko1_2.board.floor.contains 34 = true := by decide +kernel
theorem doorAt34 : soko1_2.board.doors.contains 34 = false := by decide +kernel
theorem trapAt34 : soko1_2.board.rollingTraps.contains 34 = false := by decide +kernel
theorem boxAt34 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 34 = false := rfl
theorem holeAt34 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 34 = false := rfl
theorem advanceAt34_north : advance soko1_2.board 34 .north = some 8 := by decide +kernel
theorem advanceAt34_south : advance soko1_2.board 34 .south = some 60 := by decide +kernel
theorem advanceAt34_east : advance soko1_2.board 34 .east = some 35 := by decide +kernel
theorem advanceAt34_west : advance soko1_2.board 34 .west = some 33 := by decide +kernel
theorem advanceAt34_northEast : advance soko1_2.board 34 .northEast = some 9 := by decide +kernel
theorem advanceAt34_northWest : advance soko1_2.board 34 .northWest = some 7 := by decide +kernel
theorem advanceAt34_southEast : advance soko1_2.board 34 .southEast = some 61 := by decide +kernel
theorem advanceAt34_southWest : advance soko1_2.board 34 .southWest = some 59 := by decide +kernel
theorem floorAt35 : soko1_2.board.floor.contains 35 = true := by decide +kernel
theorem doorAt35 : soko1_2.board.doors.contains 35 = false := by decide +kernel
theorem trapAt35 : soko1_2.board.rollingTraps.contains 35 = false := by decide +kernel
theorem boxAt35 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 35 = false := rfl
theorem holeAt35 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 35 = false := rfl
theorem advanceAt35_north : advance soko1_2.board 35 .north = some 9 := by decide +kernel
theorem advanceAt35_south : advance soko1_2.board 35 .south = some 61 := by decide +kernel
theorem advanceAt35_east : advance soko1_2.board 35 .east = some 36 := by decide +kernel
theorem advanceAt35_west : advance soko1_2.board 35 .west = some 34 := by decide +kernel
theorem advanceAt35_northEast : advance soko1_2.board 35 .northEast = some 10 := by decide +kernel
theorem advanceAt35_northWest : advance soko1_2.board 35 .northWest = some 8 := by decide +kernel
theorem advanceAt35_southEast : advance soko1_2.board 35 .southEast = some 62 := by decide +kernel
theorem advanceAt35_southWest : advance soko1_2.board 35 .southWest = some 60 := by decide +kernel
theorem floorAt36 : soko1_2.board.floor.contains 36 = true := by decide +kernel
theorem doorAt36 : soko1_2.board.doors.contains 36 = false := by decide +kernel
theorem trapAt36 : soko1_2.board.rollingTraps.contains 36 = false := by decide +kernel
theorem boxAt36 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 36 = false := rfl
theorem holeAt36 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 36 = true := rfl
theorem advanceAt36_north : advance soko1_2.board 36 .north = some 10 := by decide +kernel
theorem advanceAt36_south : advance soko1_2.board 36 .south = some 62 := by decide +kernel
theorem advanceAt36_east : advance soko1_2.board 36 .east = some 37 := by decide +kernel
theorem advanceAt36_west : advance soko1_2.board 36 .west = some 35 := by decide +kernel
theorem advanceAt36_northEast : advance soko1_2.board 36 .northEast = some 11 := by decide +kernel
theorem advanceAt36_northWest : advance soko1_2.board 36 .northWest = some 9 := by decide +kernel
theorem advanceAt36_southEast : advance soko1_2.board 36 .southEast = some 63 := by decide +kernel
theorem advanceAt36_southWest : advance soko1_2.board 36 .southWest = some 61 := by decide +kernel
theorem floorAt37 : soko1_2.board.floor.contains 37 = true := by decide +kernel
theorem doorAt37 : soko1_2.board.doors.contains 37 = false := by decide +kernel
theorem trapAt37 : soko1_2.board.rollingTraps.contains 37 = false := by decide +kernel
theorem boxAt37 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 37 = false := rfl
theorem holeAt37 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 37 = true := rfl
theorem advanceAt37_north : advance soko1_2.board 37 .north = some 11 := by decide +kernel
theorem advanceAt37_south : advance soko1_2.board 37 .south = some 63 := by decide +kernel
theorem advanceAt37_east : advance soko1_2.board 37 .east = some 38 := by decide +kernel
theorem advanceAt37_west : advance soko1_2.board 37 .west = some 36 := by decide +kernel
theorem advanceAt37_northEast : advance soko1_2.board 37 .northEast = some 12 := by decide +kernel
theorem advanceAt37_northWest : advance soko1_2.board 37 .northWest = some 10 := by decide +kernel
theorem advanceAt37_southEast : advance soko1_2.board 37 .southEast = some 64 := by decide +kernel
theorem advanceAt37_southWest : advance soko1_2.board 37 .southWest = some 62 := by decide +kernel
theorem floorAt38 : soko1_2.board.floor.contains 38 = true := by decide +kernel
theorem doorAt38 : soko1_2.board.doors.contains 38 = false := by decide +kernel
theorem trapAt38 : soko1_2.board.rollingTraps.contains 38 = false := by decide +kernel
theorem boxAt38 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 38 = false := rfl
theorem holeAt38 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 38 = true := rfl
theorem advanceAt38_north : advance soko1_2.board 38 .north = some 12 := by decide +kernel
theorem advanceAt38_south : advance soko1_2.board 38 .south = some 64 := by decide +kernel
theorem advanceAt38_east : advance soko1_2.board 38 .east = some 39 := by decide +kernel
theorem advanceAt38_west : advance soko1_2.board 38 .west = some 37 := by decide +kernel
theorem advanceAt38_northEast : advance soko1_2.board 38 .northEast = some 13 := by decide +kernel
theorem advanceAt38_northWest : advance soko1_2.board 38 .northWest = some 11 := by decide +kernel
theorem advanceAt38_southEast : advance soko1_2.board 38 .southEast = some 65 := by decide +kernel
theorem advanceAt38_southWest : advance soko1_2.board 38 .southWest = some 63 := by decide +kernel
theorem floorAt39 : soko1_2.board.floor.contains 39 = true := by decide +kernel
theorem doorAt39 : soko1_2.board.doors.contains 39 = false := by decide +kernel
theorem trapAt39 : soko1_2.board.rollingTraps.contains 39 = false := by decide +kernel
theorem boxAt39 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 39 = false := rfl
theorem holeAt39 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 39 = true := rfl
theorem advanceAt39_north : advance soko1_2.board 39 .north = some 13 := by decide +kernel
theorem advanceAt39_south : advance soko1_2.board 39 .south = some 65 := by decide +kernel
theorem advanceAt39_east : advance soko1_2.board 39 .east = some 40 := by decide +kernel
theorem advanceAt39_west : advance soko1_2.board 39 .west = some 38 := by decide +kernel
theorem advanceAt39_northEast : advance soko1_2.board 39 .northEast = some 14 := by decide +kernel
theorem advanceAt39_northWest : advance soko1_2.board 39 .northWest = some 12 := by decide +kernel
theorem advanceAt39_southEast : advance soko1_2.board 39 .southEast = some 66 := by decide +kernel
theorem advanceAt39_southWest : advance soko1_2.board 39 .southWest = some 64 := by decide +kernel
end NetHack.Soko12Forward220.Unified.P04
