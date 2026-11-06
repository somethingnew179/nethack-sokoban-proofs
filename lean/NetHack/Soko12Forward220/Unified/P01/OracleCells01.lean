import NetHack.Soko12Forward220.Unified.P01.OracleCells00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P01
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem floorAt40 : soko1_2.board.floor.contains 40 = true := by decide +kernel
theorem doorAt40 : soko1_2.board.doors.contains 40 = false := by decide +kernel
theorem trapAt40 : soko1_2.board.rollingTraps.contains 40 = false := by decide +kernel
theorem boxAt40 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p 40 = false := rfl
theorem holeAt40 (p : Pattern) : project (soko1_2.initial.holes.drop 1) 40 = true := rfl
theorem advanceAt40_north : advance soko1_2.board 40 .north = some 14 := by decide +kernel
theorem advanceAt40_south : advance soko1_2.board 40 .south = some 66 := by decide +kernel
theorem advanceAt40_east : advance soko1_2.board 40 .east = some 41 := by decide +kernel
theorem advanceAt40_west : advance soko1_2.board 40 .west = some 39 := by decide +kernel
theorem advanceAt40_northEast : advance soko1_2.board 40 .northEast = some 15 := by decide +kernel
theorem advanceAt40_northWest : advance soko1_2.board 40 .northWest = some 13 := by decide +kernel
theorem advanceAt40_southEast : advance soko1_2.board 40 .southEast = some 67 := by decide +kernel
theorem advanceAt40_southWest : advance soko1_2.board 40 .southWest = some 65 := by decide +kernel
theorem floorAt41 : soko1_2.board.floor.contains 41 = true := by decide +kernel
theorem doorAt41 : soko1_2.board.doors.contains 41 = false := by decide +kernel
theorem trapAt41 : soko1_2.board.rollingTraps.contains 41 = false := by decide +kernel
theorem boxAt41 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p 41 = false := rfl
theorem holeAt41 (p : Pattern) : project (soko1_2.initial.holes.drop 1) 41 = true := rfl
theorem advanceAt41_north : advance soko1_2.board 41 .north = some 15 := by decide +kernel
theorem advanceAt41_south : advance soko1_2.board 41 .south = some 67 := by decide +kernel
theorem advanceAt41_east : advance soko1_2.board 41 .east = some 42 := by decide +kernel
theorem advanceAt41_west : advance soko1_2.board 41 .west = some 40 := by decide +kernel
theorem advanceAt41_northEast : advance soko1_2.board 41 .northEast = some 16 := by decide +kernel
theorem advanceAt41_northWest : advance soko1_2.board 41 .northWest = some 14 := by decide +kernel
theorem advanceAt41_southEast : advance soko1_2.board 41 .southEast = some 68 := by decide +kernel
theorem advanceAt41_southWest : advance soko1_2.board 41 .southWest = some 66 := by decide +kernel
theorem floorAt42 : soko1_2.board.floor.contains 42 = true := by decide +kernel
theorem doorAt42 : soko1_2.board.doors.contains 42 = false := by decide +kernel
theorem trapAt42 : soko1_2.board.rollingTraps.contains 42 = false := by decide +kernel
theorem boxAt42 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p 42 = false := rfl
theorem holeAt42 (p : Pattern) : project (soko1_2.initial.holes.drop 1) 42 = true := rfl
theorem advanceAt42_north : advance soko1_2.board 42 .north = some 16 := by decide +kernel
theorem advanceAt42_south : advance soko1_2.board 42 .south = some 68 := by decide +kernel
theorem advanceAt42_east : advance soko1_2.board 42 .east = some 43 := by decide +kernel
theorem advanceAt42_west : advance soko1_2.board 42 .west = some 41 := by decide +kernel
theorem advanceAt42_northEast : advance soko1_2.board 42 .northEast = some 17 := by decide +kernel
theorem advanceAt42_northWest : advance soko1_2.board 42 .northWest = some 15 := by decide +kernel
theorem advanceAt42_southEast : advance soko1_2.board 42 .southEast = some 69 := by decide +kernel
theorem advanceAt42_southWest : advance soko1_2.board 42 .southWest = some 67 := by decide +kernel
theorem floorAt43 : soko1_2.board.floor.contains 43 = true := by decide +kernel
theorem doorAt43 : soko1_2.board.doors.contains 43 = false := by decide +kernel
theorem trapAt43 : soko1_2.board.rollingTraps.contains 43 = false := by decide +kernel
theorem boxAt43 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p 43 = false := rfl
theorem holeAt43 (p : Pattern) : project (soko1_2.initial.holes.drop 1) 43 = true := rfl
theorem advanceAt43_north : advance soko1_2.board 43 .north = some 17 := by decide +kernel
theorem advanceAt43_south : advance soko1_2.board 43 .south = some 69 := by decide +kernel
theorem advanceAt43_east : advance soko1_2.board 43 .east = some 44 := by decide +kernel
theorem advanceAt43_west : advance soko1_2.board 43 .west = some 42 := by decide +kernel
theorem advanceAt43_northEast : advance soko1_2.board 43 .northEast = some 18 := by decide +kernel
theorem advanceAt43_northWest : advance soko1_2.board 43 .northWest = some 16 := by decide +kernel
theorem advanceAt43_southEast : advance soko1_2.board 43 .southEast = some 70 := by decide +kernel
theorem advanceAt43_southWest : advance soko1_2.board 43 .southWest = some 68 := by decide +kernel
theorem floorAt44 : soko1_2.board.floor.contains 44 = true := by decide +kernel
theorem doorAt44 : soko1_2.board.doors.contains 44 = false := by decide +kernel
theorem trapAt44 : soko1_2.board.rollingTraps.contains 44 = false := by decide +kernel
theorem boxAt44 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p 44 = false := rfl
theorem holeAt44 (p : Pattern) : project (soko1_2.initial.holes.drop 1) 44 = true := rfl
theorem advanceAt44_north : advance soko1_2.board 44 .north = some 18 := by decide +kernel
theorem advanceAt44_south : advance soko1_2.board 44 .south = some 70 := by decide +kernel
theorem advanceAt44_east : advance soko1_2.board 44 .east = some 45 := by decide +kernel
theorem advanceAt44_west : advance soko1_2.board 44 .west = some 43 := by decide +kernel
theorem advanceAt44_northEast : advance soko1_2.board 44 .northEast = some 19 := by decide +kernel
theorem advanceAt44_northWest : advance soko1_2.board 44 .northWest = some 17 := by decide +kernel
theorem advanceAt44_southEast : advance soko1_2.board 44 .southEast = some 71 := by decide +kernel
theorem advanceAt44_southWest : advance soko1_2.board 44 .southWest = some 69 := by decide +kernel
theorem floorAt45 : soko1_2.board.floor.contains 45 = true := by decide +kernel
theorem doorAt45 : soko1_2.board.doors.contains 45 = false := by decide +kernel
theorem trapAt45 : soko1_2.board.rollingTraps.contains 45 = false := by decide +kernel
theorem boxAt45 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p 45 = false := rfl
theorem holeAt45 (p : Pattern) : project (soko1_2.initial.holes.drop 1) 45 = true := rfl
theorem advanceAt45_north : advance soko1_2.board 45 .north = some 19 := by decide +kernel
theorem advanceAt45_south : advance soko1_2.board 45 .south = some 71 := by decide +kernel
theorem advanceAt45_east : advance soko1_2.board 45 .east = some 46 := by decide +kernel
theorem advanceAt45_west : advance soko1_2.board 45 .west = some 44 := by decide +kernel
theorem advanceAt45_northEast : advance soko1_2.board 45 .northEast = some 20 := by decide +kernel
theorem advanceAt45_northWest : advance soko1_2.board 45 .northWest = some 18 := by decide +kernel
theorem advanceAt45_southEast : advance soko1_2.board 45 .southEast = some 72 := by decide +kernel
theorem advanceAt45_southWest : advance soko1_2.board 45 .southWest = some 70 := by decide +kernel
theorem floorAt46 : soko1_2.board.floor.contains 46 = true := by decide +kernel
theorem doorAt46 : soko1_2.board.doors.contains 46 = false := by decide +kernel
theorem trapAt46 : soko1_2.board.rollingTraps.contains 46 = false := by decide +kernel
theorem boxAt46 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p 46 = false := rfl
theorem holeAt46 (p : Pattern) : project (soko1_2.initial.holes.drop 1) 46 = true := rfl
theorem advanceAt46_north : advance soko1_2.board 46 .north = some 20 := by decide +kernel
theorem advanceAt46_south : advance soko1_2.board 46 .south = some 72 := by decide +kernel
theorem advanceAt46_east : advance soko1_2.board 46 .east = some 47 := by decide +kernel
theorem advanceAt46_west : advance soko1_2.board 46 .west = some 45 := by decide +kernel
theorem advanceAt46_northEast : advance soko1_2.board 46 .northEast = some 21 := by decide +kernel
theorem advanceAt46_northWest : advance soko1_2.board 46 .northWest = some 19 := by decide +kernel
theorem advanceAt46_southEast : advance soko1_2.board 46 .southEast = some 73 := by decide +kernel
theorem advanceAt46_southWest : advance soko1_2.board 46 .southWest = some 71 := by decide +kernel
theorem floorAt47 : soko1_2.board.floor.contains 47 = true := by decide +kernel
theorem doorAt47 : soko1_2.board.doors.contains 47 = false := by decide +kernel
theorem trapAt47 : soko1_2.board.rollingTraps.contains 47 = false := by decide +kernel
theorem boxAt47 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p 47 = false := rfl
theorem holeAt47 (p : Pattern) : project (soko1_2.initial.holes.drop 1) 47 = true := rfl
theorem advanceAt47_north : advance soko1_2.board 47 .north = some 21 := by decide +kernel
theorem advanceAt47_south : advance soko1_2.board 47 .south = some 73 := by decide +kernel
theorem advanceAt47_east : advance soko1_2.board 47 .east = some 48 := by decide +kernel
theorem advanceAt47_west : advance soko1_2.board 47 .west = some 46 := by decide +kernel
theorem advanceAt47_northEast : advance soko1_2.board 47 .northEast = some 22 := by decide +kernel
theorem advanceAt47_northWest : advance soko1_2.board 47 .northWest = some 20 := by decide +kernel
theorem advanceAt47_southEast : advance soko1_2.board 47 .southEast = some 74 := by decide +kernel
theorem advanceAt47_southWest : advance soko1_2.board 47 .southWest = some 72 := by decide +kernel
theorem floorAt48 : soko1_2.board.floor.contains 48 = true := by decide +kernel
theorem doorAt48 : soko1_2.board.doors.contains 48 = false := by decide +kernel
theorem trapAt48 : soko1_2.board.rollingTraps.contains 48 = false := by decide +kernel
theorem boxAt48 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p 48 = false := rfl
theorem holeAt48 (p : Pattern) : project (soko1_2.initial.holes.drop 1) 48 = true := rfl
theorem advanceAt48_north : advance soko1_2.board 48 .north = some 22 := by decide +kernel
theorem advanceAt48_south : advance soko1_2.board 48 .south = some 74 := by decide +kernel
theorem advanceAt48_east : advance soko1_2.board 48 .east = some 49 := by decide +kernel
theorem advanceAt48_west : advance soko1_2.board 48 .west = some 47 := by decide +kernel
theorem advanceAt48_northEast : advance soko1_2.board 48 .northEast = some 23 := by decide +kernel
theorem advanceAt48_northWest : advance soko1_2.board 48 .northWest = some 21 := by decide +kernel
theorem advanceAt48_southEast : advance soko1_2.board 48 .southEast = some 75 := by decide +kernel
theorem advanceAt48_southWest : advance soko1_2.board 48 .southWest = some 73 := by decide +kernel
theorem floorAt49 : soko1_2.board.floor.contains 49 = true := by decide +kernel
theorem doorAt49 : soko1_2.board.doors.contains 49 = false := by decide +kernel
theorem trapAt49 : soko1_2.board.rollingTraps.contains 49 = false := by decide +kernel
theorem boxAt49 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p 49 = false := rfl
theorem holeAt49 (p : Pattern) : project (soko1_2.initial.holes.drop 1) 49 = true := rfl
theorem advanceAt49_north : advance soko1_2.board 49 .north = some 23 := by decide +kernel
theorem advanceAt49_south : advance soko1_2.board 49 .south = some 75 := by decide +kernel
theorem advanceAt49_east : advance soko1_2.board 49 .east = some 50 := by decide +kernel
theorem advanceAt49_west : advance soko1_2.board 49 .west = some 48 := by decide +kernel
theorem advanceAt49_northEast : advance soko1_2.board 49 .northEast = some 24 := by decide +kernel
theorem advanceAt49_northWest : advance soko1_2.board 49 .northWest = some 22 := by decide +kernel
theorem advanceAt49_southEast : advance soko1_2.board 49 .southEast = some 76 := by decide +kernel
theorem advanceAt49_southWest : advance soko1_2.board 49 .southWest = some 74 := by decide +kernel
theorem floorAt50 : soko1_2.board.floor.contains 50 = true := by decide +kernel
theorem doorAt50 : soko1_2.board.doors.contains 50 = false := by decide +kernel
theorem trapAt50 : soko1_2.board.rollingTraps.contains 50 = false := by decide +kernel
theorem boxAt50 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p 50 = false := rfl
theorem holeAt50 (p : Pattern) : project (soko1_2.initial.holes.drop 1) 50 = false := rfl
theorem advanceAt50_north : advance soko1_2.board 50 .north = some 24 := by decide +kernel
theorem advanceAt50_south : advance soko1_2.board 50 .south = some 76 := by decide +kernel
theorem advanceAt50_east : advance soko1_2.board 50 .east = some 51 := by decide +kernel
theorem advanceAt50_west : advance soko1_2.board 50 .west = some 49 := by decide +kernel
theorem advanceAt50_northEast : advance soko1_2.board 50 .northEast = some 25 := by decide +kernel
theorem advanceAt50_northWest : advance soko1_2.board 50 .northWest = some 23 := by decide +kernel
theorem advanceAt50_southEast : advance soko1_2.board 50 .southEast = some 77 := by decide +kernel
theorem advanceAt50_southWest : advance soko1_2.board 50 .southWest = some 75 := by decide +kernel
theorem floorAt51 : soko1_2.board.floor.contains 51 = false := by decide +kernel
theorem doorAt51 : soko1_2.board.doors.contains 51 = false := by decide +kernel
theorem trapAt51 : soko1_2.board.rollingTraps.contains 51 = false := by decide +kernel
theorem boxAt51 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p 51 = false := rfl
theorem holeAt51 (p : Pattern) : project (soko1_2.initial.holes.drop 1) 51 = false := rfl
theorem advanceAt51_north : advance soko1_2.board 51 .north = some 25 := by decide +kernel
theorem advanceAt51_south : advance soko1_2.board 51 .south = some 77 := by decide +kernel
theorem advanceAt51_east : advance soko1_2.board 51 .east = none := by decide +kernel
theorem advanceAt51_west : advance soko1_2.board 51 .west = some 50 := by decide +kernel
theorem advanceAt51_northEast : advance soko1_2.board 51 .northEast = none := by decide +kernel
theorem advanceAt51_northWest : advance soko1_2.board 51 .northWest = some 24 := by decide +kernel
theorem advanceAt51_southEast : advance soko1_2.board 51 .southEast = none := by decide +kernel
theorem advanceAt51_southWest : advance soko1_2.board 51 .southWest = some 76 := by decide +kernel
theorem floorAt52 : soko1_2.board.floor.contains 52 = false := by decide +kernel
theorem doorAt52 : soko1_2.board.doors.contains 52 = false := by decide +kernel
theorem trapAt52 : soko1_2.board.rollingTraps.contains 52 = false := by decide +kernel
theorem boxAt52 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p 52 = false := rfl
theorem holeAt52 (p : Pattern) : project (soko1_2.initial.holes.drop 1) 52 = false := rfl
theorem advanceAt52_north : advance soko1_2.board 52 .north = some 26 := by decide +kernel
theorem advanceAt52_south : advance soko1_2.board 52 .south = some 78 := by decide +kernel
theorem advanceAt52_east : advance soko1_2.board 52 .east = some 53 := by decide +kernel
theorem advanceAt52_west : advance soko1_2.board 52 .west = none := by decide +kernel
theorem advanceAt52_northEast : advance soko1_2.board 52 .northEast = some 27 := by decide +kernel
theorem advanceAt52_northWest : advance soko1_2.board 52 .northWest = none := by decide +kernel
theorem advanceAt52_southEast : advance soko1_2.board 52 .southEast = some 79 := by decide +kernel
theorem advanceAt52_southWest : advance soko1_2.board 52 .southWest = none := by decide +kernel
theorem floorAt53 : soko1_2.board.floor.contains 53 = false := by decide +kernel
theorem doorAt53 : soko1_2.board.doors.contains 53 = false := by decide +kernel
theorem trapAt53 : soko1_2.board.rollingTraps.contains 53 = false := by decide +kernel
theorem boxAt53 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p 53 = false := rfl
theorem holeAt53 (p : Pattern) : project (soko1_2.initial.holes.drop 1) 53 = false := rfl
theorem advanceAt53_north : advance soko1_2.board 53 .north = some 27 := by decide +kernel
theorem advanceAt53_south : advance soko1_2.board 53 .south = some 79 := by decide +kernel
theorem advanceAt53_east : advance soko1_2.board 53 .east = some 54 := by decide +kernel
theorem advanceAt53_west : advance soko1_2.board 53 .west = some 52 := by decide +kernel
theorem advanceAt53_northEast : advance soko1_2.board 53 .northEast = some 28 := by decide +kernel
theorem advanceAt53_northWest : advance soko1_2.board 53 .northWest = some 26 := by decide +kernel
theorem advanceAt53_southEast : advance soko1_2.board 53 .southEast = some 80 := by decide +kernel
theorem advanceAt53_southWest : advance soko1_2.board 53 .southWest = some 78 := by decide +kernel
theorem floorAt54 : soko1_2.board.floor.contains 54 = false := by decide +kernel
theorem doorAt54 : soko1_2.board.doors.contains 54 = false := by decide +kernel
theorem trapAt54 : soko1_2.board.rollingTraps.contains 54 = false := by decide +kernel
theorem boxAt54 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p 54 = false := rfl
theorem holeAt54 (p : Pattern) : project (soko1_2.initial.holes.drop 1) 54 = false := rfl
theorem advanceAt54_north : advance soko1_2.board 54 .north = some 28 := by decide +kernel
theorem advanceAt54_south : advance soko1_2.board 54 .south = some 80 := by decide +kernel
theorem advanceAt54_east : advance soko1_2.board 54 .east = some 55 := by decide +kernel
theorem advanceAt54_west : advance soko1_2.board 54 .west = some 53 := by decide +kernel
theorem advanceAt54_northEast : advance soko1_2.board 54 .northEast = some 29 := by decide +kernel
theorem advanceAt54_northWest : advance soko1_2.board 54 .northWest = some 27 := by decide +kernel
theorem advanceAt54_southEast : advance soko1_2.board 54 .southEast = some 81 := by decide +kernel
theorem advanceAt54_southWest : advance soko1_2.board 54 .southWest = some 79 := by decide +kernel
theorem floorAt55 : soko1_2.board.floor.contains 55 = true := by decide +kernel
theorem doorAt55 : soko1_2.board.doors.contains 55 = false := by decide +kernel
theorem trapAt55 : soko1_2.board.rollingTraps.contains 55 = false := by decide +kernel
theorem boxAt55 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p 55 = false := rfl
theorem holeAt55 (p : Pattern) : project (soko1_2.initial.holes.drop 1) 55 = false := rfl
theorem advanceAt55_north : advance soko1_2.board 55 .north = some 29 := by decide +kernel
theorem advanceAt55_south : advance soko1_2.board 55 .south = some 81 := by decide +kernel
theorem advanceAt55_east : advance soko1_2.board 55 .east = some 56 := by decide +kernel
theorem advanceAt55_west : advance soko1_2.board 55 .west = some 54 := by decide +kernel
theorem advanceAt55_northEast : advance soko1_2.board 55 .northEast = some 30 := by decide +kernel
theorem advanceAt55_northWest : advance soko1_2.board 55 .northWest = some 28 := by decide +kernel
theorem advanceAt55_southEast : advance soko1_2.board 55 .southEast = some 82 := by decide +kernel
theorem advanceAt55_southWest : advance soko1_2.board 55 .southWest = some 80 := by decide +kernel
theorem floorAt56 : soko1_2.board.floor.contains 56 = true := by decide +kernel
theorem doorAt56 : soko1_2.board.doors.contains 56 = false := by decide +kernel
theorem trapAt56 : soko1_2.board.rollingTraps.contains 56 = false := by decide +kernel
theorem boxAt56 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p 56 = p 56 := rfl
theorem holeAt56 (p : Pattern) : project (soko1_2.initial.holes.drop 1) 56 = false := rfl
theorem advanceAt56_north : advance soko1_2.board 56 .north = some 30 := by decide +kernel
theorem advanceAt56_south : advance soko1_2.board 56 .south = some 82 := by decide +kernel
theorem advanceAt56_east : advance soko1_2.board 56 .east = some 57 := by decide +kernel
theorem advanceAt56_west : advance soko1_2.board 56 .west = some 55 := by decide +kernel
theorem advanceAt56_northEast : advance soko1_2.board 56 .northEast = some 31 := by decide +kernel
theorem advanceAt56_northWest : advance soko1_2.board 56 .northWest = some 29 := by decide +kernel
theorem advanceAt56_southEast : advance soko1_2.board 56 .southEast = some 83 := by decide +kernel
theorem advanceAt56_southWest : advance soko1_2.board 56 .southWest = some 81 := by decide +kernel
theorem floorAt57 : soko1_2.board.floor.contains 57 = false := by decide +kernel
theorem doorAt57 : soko1_2.board.doors.contains 57 = false := by decide +kernel
theorem trapAt57 : soko1_2.board.rollingTraps.contains 57 = false := by decide +kernel
theorem boxAt57 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p 57 = false := rfl
theorem holeAt57 (p : Pattern) : project (soko1_2.initial.holes.drop 1) 57 = false := rfl
theorem advanceAt57_north : advance soko1_2.board 57 .north = some 31 := by decide +kernel
theorem advanceAt57_south : advance soko1_2.board 57 .south = some 83 := by decide +kernel
theorem advanceAt57_east : advance soko1_2.board 57 .east = some 58 := by decide +kernel
theorem advanceAt57_west : advance soko1_2.board 57 .west = some 56 := by decide +kernel
theorem advanceAt57_northEast : advance soko1_2.board 57 .northEast = some 32 := by decide +kernel
theorem advanceAt57_northWest : advance soko1_2.board 57 .northWest = some 30 := by decide +kernel
theorem advanceAt57_southEast : advance soko1_2.board 57 .southEast = some 84 := by decide +kernel
theorem advanceAt57_southWest : advance soko1_2.board 57 .southWest = some 82 := by decide +kernel
theorem floorAt58 : soko1_2.board.floor.contains 58 = false := by decide +kernel
theorem doorAt58 : soko1_2.board.doors.contains 58 = false := by decide +kernel
theorem trapAt58 : soko1_2.board.rollingTraps.contains 58 = false := by decide +kernel
theorem boxAt58 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p 58 = false := rfl
theorem holeAt58 (p : Pattern) : project (soko1_2.initial.holes.drop 1) 58 = false := rfl
theorem advanceAt58_north : advance soko1_2.board 58 .north = some 32 := by decide +kernel
theorem advanceAt58_south : advance soko1_2.board 58 .south = some 84 := by decide +kernel
theorem advanceAt58_east : advance soko1_2.board 58 .east = some 59 := by decide +kernel
theorem advanceAt58_west : advance soko1_2.board 58 .west = some 57 := by decide +kernel
theorem advanceAt58_northEast : advance soko1_2.board 58 .northEast = some 33 := by decide +kernel
theorem advanceAt58_northWest : advance soko1_2.board 58 .northWest = some 31 := by decide +kernel
theorem advanceAt58_southEast : advance soko1_2.board 58 .southEast = some 85 := by decide +kernel
theorem advanceAt58_southWest : advance soko1_2.board 58 .southWest = some 83 := by decide +kernel
theorem floorAt59 : soko1_2.board.floor.contains 59 = false := by decide +kernel
theorem doorAt59 : soko1_2.board.doors.contains 59 = false := by decide +kernel
theorem trapAt59 : soko1_2.board.rollingTraps.contains 59 = false := by decide +kernel
theorem boxAt59 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p 59 = false := rfl
theorem holeAt59 (p : Pattern) : project (soko1_2.initial.holes.drop 1) 59 = false := rfl
theorem advanceAt59_north : advance soko1_2.board 59 .north = some 33 := by decide +kernel
theorem advanceAt59_south : advance soko1_2.board 59 .south = some 85 := by decide +kernel
theorem advanceAt59_east : advance soko1_2.board 59 .east = some 60 := by decide +kernel
theorem advanceAt59_west : advance soko1_2.board 59 .west = some 58 := by decide +kernel
theorem advanceAt59_northEast : advance soko1_2.board 59 .northEast = some 34 := by decide +kernel
theorem advanceAt59_northWest : advance soko1_2.board 59 .northWest = some 32 := by decide +kernel
theorem advanceAt59_southEast : advance soko1_2.board 59 .southEast = some 86 := by decide +kernel
theorem advanceAt59_southWest : advance soko1_2.board 59 .southWest = some 84 := by decide +kernel
theorem floorAt60 : soko1_2.board.floor.contains 60 = false := by decide +kernel
theorem doorAt60 : soko1_2.board.doors.contains 60 = false := by decide +kernel
theorem trapAt60 : soko1_2.board.rollingTraps.contains 60 = false := by decide +kernel
theorem boxAt60 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p 60 = false := rfl
theorem holeAt60 (p : Pattern) : project (soko1_2.initial.holes.drop 1) 60 = false := rfl
theorem advanceAt60_north : advance soko1_2.board 60 .north = some 34 := by decide +kernel
theorem advanceAt60_south : advance soko1_2.board 60 .south = some 86 := by decide +kernel
theorem advanceAt60_east : advance soko1_2.board 60 .east = some 61 := by decide +kernel
theorem advanceAt60_west : advance soko1_2.board 60 .west = some 59 := by decide +kernel
theorem advanceAt60_northEast : advance soko1_2.board 60 .northEast = some 35 := by decide +kernel
theorem advanceAt60_northWest : advance soko1_2.board 60 .northWest = some 33 := by decide +kernel
theorem advanceAt60_southEast : advance soko1_2.board 60 .southEast = some 87 := by decide +kernel
theorem advanceAt60_southWest : advance soko1_2.board 60 .southWest = some 85 := by decide +kernel
theorem floorAt61 : soko1_2.board.floor.contains 61 = false := by decide +kernel
theorem doorAt61 : soko1_2.board.doors.contains 61 = false := by decide +kernel
theorem trapAt61 : soko1_2.board.rollingTraps.contains 61 = false := by decide +kernel
theorem boxAt61 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p 61 = false := rfl
theorem holeAt61 (p : Pattern) : project (soko1_2.initial.holes.drop 1) 61 = false := rfl
theorem advanceAt61_north : advance soko1_2.board 61 .north = some 35 := by decide +kernel
theorem advanceAt61_south : advance soko1_2.board 61 .south = some 87 := by decide +kernel
theorem advanceAt61_east : advance soko1_2.board 61 .east = some 62 := by decide +kernel
theorem advanceAt61_west : advance soko1_2.board 61 .west = some 60 := by decide +kernel
theorem advanceAt61_northEast : advance soko1_2.board 61 .northEast = some 36 := by decide +kernel
theorem advanceAt61_northWest : advance soko1_2.board 61 .northWest = some 34 := by decide +kernel
theorem advanceAt61_southEast : advance soko1_2.board 61 .southEast = some 88 := by decide +kernel
theorem advanceAt61_southWest : advance soko1_2.board 61 .southWest = some 86 := by decide +kernel
theorem floorAt62 : soko1_2.board.floor.contains 62 = false := by decide +kernel
theorem doorAt62 : soko1_2.board.doors.contains 62 = false := by decide +kernel
theorem trapAt62 : soko1_2.board.rollingTraps.contains 62 = false := by decide +kernel
theorem boxAt62 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p 62 = false := rfl
theorem holeAt62 (p : Pattern) : project (soko1_2.initial.holes.drop 1) 62 = false := rfl
theorem advanceAt62_north : advance soko1_2.board 62 .north = some 36 := by decide +kernel
theorem advanceAt62_south : advance soko1_2.board 62 .south = some 88 := by decide +kernel
theorem advanceAt62_east : advance soko1_2.board 62 .east = some 63 := by decide +kernel
theorem advanceAt62_west : advance soko1_2.board 62 .west = some 61 := by decide +kernel
theorem advanceAt62_northEast : advance soko1_2.board 62 .northEast = some 37 := by decide +kernel
theorem advanceAt62_northWest : advance soko1_2.board 62 .northWest = some 35 := by decide +kernel
theorem advanceAt62_southEast : advance soko1_2.board 62 .southEast = some 89 := by decide +kernel
theorem advanceAt62_southWest : advance soko1_2.board 62 .southWest = some 87 := by decide +kernel
theorem floorAt63 : soko1_2.board.floor.contains 63 = false := by decide +kernel
theorem doorAt63 : soko1_2.board.doors.contains 63 = false := by decide +kernel
theorem trapAt63 : soko1_2.board.rollingTraps.contains 63 = false := by decide +kernel
theorem boxAt63 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p 63 = false := rfl
theorem holeAt63 (p : Pattern) : project (soko1_2.initial.holes.drop 1) 63 = false := rfl
theorem advanceAt63_north : advance soko1_2.board 63 .north = some 37 := by decide +kernel
theorem advanceAt63_south : advance soko1_2.board 63 .south = some 89 := by decide +kernel
theorem advanceAt63_east : advance soko1_2.board 63 .east = some 64 := by decide +kernel
theorem advanceAt63_west : advance soko1_2.board 63 .west = some 62 := by decide +kernel
theorem advanceAt63_northEast : advance soko1_2.board 63 .northEast = some 38 := by decide +kernel
theorem advanceAt63_northWest : advance soko1_2.board 63 .northWest = some 36 := by decide +kernel
theorem advanceAt63_southEast : advance soko1_2.board 63 .southEast = some 90 := by decide +kernel
theorem advanceAt63_southWest : advance soko1_2.board 63 .southWest = some 88 := by decide +kernel
theorem floorAt64 : soko1_2.board.floor.contains 64 = false := by decide +kernel
theorem doorAt64 : soko1_2.board.doors.contains 64 = false := by decide +kernel
theorem trapAt64 : soko1_2.board.rollingTraps.contains 64 = false := by decide +kernel
theorem boxAt64 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p 64 = false := rfl
theorem holeAt64 (p : Pattern) : project (soko1_2.initial.holes.drop 1) 64 = false := rfl
theorem advanceAt64_north : advance soko1_2.board 64 .north = some 38 := by decide +kernel
theorem advanceAt64_south : advance soko1_2.board 64 .south = some 90 := by decide +kernel
theorem advanceAt64_east : advance soko1_2.board 64 .east = some 65 := by decide +kernel
theorem advanceAt64_west : advance soko1_2.board 64 .west = some 63 := by decide +kernel
theorem advanceAt64_northEast : advance soko1_2.board 64 .northEast = some 39 := by decide +kernel
theorem advanceAt64_northWest : advance soko1_2.board 64 .northWest = some 37 := by decide +kernel
theorem advanceAt64_southEast : advance soko1_2.board 64 .southEast = some 91 := by decide +kernel
theorem advanceAt64_southWest : advance soko1_2.board 64 .southWest = some 89 := by decide +kernel
theorem floorAt65 : soko1_2.board.floor.contains 65 = false := by decide +kernel
theorem doorAt65 : soko1_2.board.doors.contains 65 = false := by decide +kernel
theorem trapAt65 : soko1_2.board.rollingTraps.contains 65 = false := by decide +kernel
theorem boxAt65 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p 65 = false := rfl
theorem holeAt65 (p : Pattern) : project (soko1_2.initial.holes.drop 1) 65 = false := rfl
theorem advanceAt65_north : advance soko1_2.board 65 .north = some 39 := by decide +kernel
theorem advanceAt65_south : advance soko1_2.board 65 .south = some 91 := by decide +kernel
theorem advanceAt65_east : advance soko1_2.board 65 .east = some 66 := by decide +kernel
theorem advanceAt65_west : advance soko1_2.board 65 .west = some 64 := by decide +kernel
theorem advanceAt65_northEast : advance soko1_2.board 65 .northEast = some 40 := by decide +kernel
theorem advanceAt65_northWest : advance soko1_2.board 65 .northWest = some 38 := by decide +kernel
theorem advanceAt65_southEast : advance soko1_2.board 65 .southEast = some 92 := by decide +kernel
theorem advanceAt65_southWest : advance soko1_2.board 65 .southWest = some 90 := by decide +kernel
theorem floorAt66 : soko1_2.board.floor.contains 66 = false := by decide +kernel
theorem doorAt66 : soko1_2.board.doors.contains 66 = false := by decide +kernel
theorem trapAt66 : soko1_2.board.rollingTraps.contains 66 = false := by decide +kernel
theorem boxAt66 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p 66 = false := rfl
theorem holeAt66 (p : Pattern) : project (soko1_2.initial.holes.drop 1) 66 = false := rfl
theorem advanceAt66_north : advance soko1_2.board 66 .north = some 40 := by decide +kernel
theorem advanceAt66_south : advance soko1_2.board 66 .south = some 92 := by decide +kernel
theorem advanceAt66_east : advance soko1_2.board 66 .east = some 67 := by decide +kernel
theorem advanceAt66_west : advance soko1_2.board 66 .west = some 65 := by decide +kernel
theorem advanceAt66_northEast : advance soko1_2.board 66 .northEast = some 41 := by decide +kernel
theorem advanceAt66_northWest : advance soko1_2.board 66 .northWest = some 39 := by decide +kernel
theorem advanceAt66_southEast : advance soko1_2.board 66 .southEast = some 93 := by decide +kernel
theorem advanceAt66_southWest : advance soko1_2.board 66 .southWest = some 91 := by decide +kernel
theorem floorAt67 : soko1_2.board.floor.contains 67 = false := by decide +kernel
theorem doorAt67 : soko1_2.board.doors.contains 67 = false := by decide +kernel
theorem trapAt67 : soko1_2.board.rollingTraps.contains 67 = false := by decide +kernel
theorem boxAt67 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p 67 = false := rfl
theorem holeAt67 (p : Pattern) : project (soko1_2.initial.holes.drop 1) 67 = false := rfl
theorem advanceAt67_north : advance soko1_2.board 67 .north = some 41 := by decide +kernel
theorem advanceAt67_south : advance soko1_2.board 67 .south = some 93 := by decide +kernel
theorem advanceAt67_east : advance soko1_2.board 67 .east = some 68 := by decide +kernel
theorem advanceAt67_west : advance soko1_2.board 67 .west = some 66 := by decide +kernel
theorem advanceAt67_northEast : advance soko1_2.board 67 .northEast = some 42 := by decide +kernel
theorem advanceAt67_northWest : advance soko1_2.board 67 .northWest = some 40 := by decide +kernel
theorem advanceAt67_southEast : advance soko1_2.board 67 .southEast = some 94 := by decide +kernel
theorem advanceAt67_southWest : advance soko1_2.board 67 .southWest = some 92 := by decide +kernel
theorem floorAt68 : soko1_2.board.floor.contains 68 = false := by decide +kernel
theorem doorAt68 : soko1_2.board.doors.contains 68 = false := by decide +kernel
theorem trapAt68 : soko1_2.board.rollingTraps.contains 68 = false := by decide +kernel
theorem boxAt68 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p 68 = false := rfl
theorem holeAt68 (p : Pattern) : project (soko1_2.initial.holes.drop 1) 68 = false := rfl
theorem advanceAt68_north : advance soko1_2.board 68 .north = some 42 := by decide +kernel
theorem advanceAt68_south : advance soko1_2.board 68 .south = some 94 := by decide +kernel
theorem advanceAt68_east : advance soko1_2.board 68 .east = some 69 := by decide +kernel
theorem advanceAt68_west : advance soko1_2.board 68 .west = some 67 := by decide +kernel
theorem advanceAt68_northEast : advance soko1_2.board 68 .northEast = some 43 := by decide +kernel
theorem advanceAt68_northWest : advance soko1_2.board 68 .northWest = some 41 := by decide +kernel
theorem advanceAt68_southEast : advance soko1_2.board 68 .southEast = some 95 := by decide +kernel
theorem advanceAt68_southWest : advance soko1_2.board 68 .southWest = some 93 := by decide +kernel
theorem floorAt69 : soko1_2.board.floor.contains 69 = false := by decide +kernel
theorem doorAt69 : soko1_2.board.doors.contains 69 = false := by decide +kernel
theorem trapAt69 : soko1_2.board.rollingTraps.contains 69 = false := by decide +kernel
theorem boxAt69 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p 69 = false := rfl
theorem holeAt69 (p : Pattern) : project (soko1_2.initial.holes.drop 1) 69 = false := rfl
theorem advanceAt69_north : advance soko1_2.board 69 .north = some 43 := by decide +kernel
theorem advanceAt69_south : advance soko1_2.board 69 .south = some 95 := by decide +kernel
theorem advanceAt69_east : advance soko1_2.board 69 .east = some 70 := by decide +kernel
theorem advanceAt69_west : advance soko1_2.board 69 .west = some 68 := by decide +kernel
theorem advanceAt69_northEast : advance soko1_2.board 69 .northEast = some 44 := by decide +kernel
theorem advanceAt69_northWest : advance soko1_2.board 69 .northWest = some 42 := by decide +kernel
theorem advanceAt69_southEast : advance soko1_2.board 69 .southEast = some 96 := by decide +kernel
theorem advanceAt69_southWest : advance soko1_2.board 69 .southWest = some 94 := by decide +kernel
theorem floorAt70 : soko1_2.board.floor.contains 70 = false := by decide +kernel
theorem doorAt70 : soko1_2.board.doors.contains 70 = false := by decide +kernel
theorem trapAt70 : soko1_2.board.rollingTraps.contains 70 = false := by decide +kernel
theorem boxAt70 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p 70 = false := rfl
theorem holeAt70 (p : Pattern) : project (soko1_2.initial.holes.drop 1) 70 = false := rfl
theorem advanceAt70_north : advance soko1_2.board 70 .north = some 44 := by decide +kernel
theorem advanceAt70_south : advance soko1_2.board 70 .south = some 96 := by decide +kernel
theorem advanceAt70_east : advance soko1_2.board 70 .east = some 71 := by decide +kernel
theorem advanceAt70_west : advance soko1_2.board 70 .west = some 69 := by decide +kernel
theorem advanceAt70_northEast : advance soko1_2.board 70 .northEast = some 45 := by decide +kernel
theorem advanceAt70_northWest : advance soko1_2.board 70 .northWest = some 43 := by decide +kernel
theorem advanceAt70_southEast : advance soko1_2.board 70 .southEast = some 97 := by decide +kernel
theorem advanceAt70_southWest : advance soko1_2.board 70 .southWest = some 95 := by decide +kernel
theorem floorAt71 : soko1_2.board.floor.contains 71 = false := by decide +kernel
theorem doorAt71 : soko1_2.board.doors.contains 71 = false := by decide +kernel
theorem trapAt71 : soko1_2.board.rollingTraps.contains 71 = false := by decide +kernel
theorem boxAt71 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p 71 = false := rfl
theorem holeAt71 (p : Pattern) : project (soko1_2.initial.holes.drop 1) 71 = false := rfl
theorem advanceAt71_north : advance soko1_2.board 71 .north = some 45 := by decide +kernel
theorem advanceAt71_south : advance soko1_2.board 71 .south = some 97 := by decide +kernel
theorem advanceAt71_east : advance soko1_2.board 71 .east = some 72 := by decide +kernel
theorem advanceAt71_west : advance soko1_2.board 71 .west = some 70 := by decide +kernel
theorem advanceAt71_northEast : advance soko1_2.board 71 .northEast = some 46 := by decide +kernel
theorem advanceAt71_northWest : advance soko1_2.board 71 .northWest = some 44 := by decide +kernel
theorem advanceAt71_southEast : advance soko1_2.board 71 .southEast = some 98 := by decide +kernel
theorem advanceAt71_southWest : advance soko1_2.board 71 .southWest = some 96 := by decide +kernel
theorem floorAt72 : soko1_2.board.floor.contains 72 = false := by decide +kernel
theorem doorAt72 : soko1_2.board.doors.contains 72 = false := by decide +kernel
theorem trapAt72 : soko1_2.board.rollingTraps.contains 72 = false := by decide +kernel
theorem boxAt72 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p 72 = false := rfl
theorem holeAt72 (p : Pattern) : project (soko1_2.initial.holes.drop 1) 72 = false := rfl
theorem advanceAt72_north : advance soko1_2.board 72 .north = some 46 := by decide +kernel
theorem advanceAt72_south : advance soko1_2.board 72 .south = some 98 := by decide +kernel
theorem advanceAt72_east : advance soko1_2.board 72 .east = some 73 := by decide +kernel
theorem advanceAt72_west : advance soko1_2.board 72 .west = some 71 := by decide +kernel
theorem advanceAt72_northEast : advance soko1_2.board 72 .northEast = some 47 := by decide +kernel
theorem advanceAt72_northWest : advance soko1_2.board 72 .northWest = some 45 := by decide +kernel
theorem advanceAt72_southEast : advance soko1_2.board 72 .southEast = some 99 := by decide +kernel
theorem advanceAt72_southWest : advance soko1_2.board 72 .southWest = some 97 := by decide +kernel
theorem floorAt73 : soko1_2.board.floor.contains 73 = false := by decide +kernel
theorem doorAt73 : soko1_2.board.doors.contains 73 = false := by decide +kernel
theorem trapAt73 : soko1_2.board.rollingTraps.contains 73 = false := by decide +kernel
theorem boxAt73 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p 73 = false := rfl
theorem holeAt73 (p : Pattern) : project (soko1_2.initial.holes.drop 1) 73 = false := rfl
theorem advanceAt73_north : advance soko1_2.board 73 .north = some 47 := by decide +kernel
theorem advanceAt73_south : advance soko1_2.board 73 .south = some 99 := by decide +kernel
theorem advanceAt73_east : advance soko1_2.board 73 .east = some 74 := by decide +kernel
theorem advanceAt73_west : advance soko1_2.board 73 .west = some 72 := by decide +kernel
theorem advanceAt73_northEast : advance soko1_2.board 73 .northEast = some 48 := by decide +kernel
theorem advanceAt73_northWest : advance soko1_2.board 73 .northWest = some 46 := by decide +kernel
theorem advanceAt73_southEast : advance soko1_2.board 73 .southEast = some 100 := by decide +kernel
theorem advanceAt73_southWest : advance soko1_2.board 73 .southWest = some 98 := by decide +kernel
theorem floorAt74 : soko1_2.board.floor.contains 74 = false := by decide +kernel
theorem doorAt74 : soko1_2.board.doors.contains 74 = false := by decide +kernel
theorem trapAt74 : soko1_2.board.rollingTraps.contains 74 = false := by decide +kernel
theorem boxAt74 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p 74 = false := rfl
theorem holeAt74 (p : Pattern) : project (soko1_2.initial.holes.drop 1) 74 = false := rfl
theorem advanceAt74_north : advance soko1_2.board 74 .north = some 48 := by decide +kernel
theorem advanceAt74_south : advance soko1_2.board 74 .south = some 100 := by decide +kernel
theorem advanceAt74_east : advance soko1_2.board 74 .east = some 75 := by decide +kernel
theorem advanceAt74_west : advance soko1_2.board 74 .west = some 73 := by decide +kernel
theorem advanceAt74_northEast : advance soko1_2.board 74 .northEast = some 49 := by decide +kernel
theorem advanceAt74_northWest : advance soko1_2.board 74 .northWest = some 47 := by decide +kernel
theorem advanceAt74_southEast : advance soko1_2.board 74 .southEast = some 101 := by decide +kernel
theorem advanceAt74_southWest : advance soko1_2.board 74 .southWest = some 99 := by decide +kernel
theorem floorAt75 : soko1_2.board.floor.contains 75 = false := by decide +kernel
theorem doorAt75 : soko1_2.board.doors.contains 75 = false := by decide +kernel
theorem trapAt75 : soko1_2.board.rollingTraps.contains 75 = false := by decide +kernel
theorem boxAt75 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p 75 = false := rfl
theorem holeAt75 (p : Pattern) : project (soko1_2.initial.holes.drop 1) 75 = false := rfl
theorem advanceAt75_north : advance soko1_2.board 75 .north = some 49 := by decide +kernel
theorem advanceAt75_south : advance soko1_2.board 75 .south = some 101 := by decide +kernel
theorem advanceAt75_east : advance soko1_2.board 75 .east = some 76 := by decide +kernel
theorem advanceAt75_west : advance soko1_2.board 75 .west = some 74 := by decide +kernel
theorem advanceAt75_northEast : advance soko1_2.board 75 .northEast = some 50 := by decide +kernel
theorem advanceAt75_northWest : advance soko1_2.board 75 .northWest = some 48 := by decide +kernel
theorem advanceAt75_southEast : advance soko1_2.board 75 .southEast = some 102 := by decide +kernel
theorem advanceAt75_southWest : advance soko1_2.board 75 .southWest = some 100 := by decide +kernel
theorem floorAt76 : soko1_2.board.floor.contains 76 = true := by decide +kernel
theorem doorAt76 : soko1_2.board.doors.contains 76 = false := by decide +kernel
theorem trapAt76 : soko1_2.board.rollingTraps.contains 76 = false := by decide +kernel
theorem boxAt76 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p 76 = false := rfl
theorem holeAt76 (p : Pattern) : project (soko1_2.initial.holes.drop 1) 76 = false := rfl
theorem advanceAt76_north : advance soko1_2.board 76 .north = some 50 := by decide +kernel
theorem advanceAt76_south : advance soko1_2.board 76 .south = some 102 := by decide +kernel
theorem advanceAt76_east : advance soko1_2.board 76 .east = some 77 := by decide +kernel
theorem advanceAt76_west : advance soko1_2.board 76 .west = some 75 := by decide +kernel
theorem advanceAt76_northEast : advance soko1_2.board 76 .northEast = some 51 := by decide +kernel
theorem advanceAt76_northWest : advance soko1_2.board 76 .northWest = some 49 := by decide +kernel
theorem advanceAt76_southEast : advance soko1_2.board 76 .southEast = some 103 := by decide +kernel
theorem advanceAt76_southWest : advance soko1_2.board 76 .southWest = some 101 := by decide +kernel
theorem floorAt77 : soko1_2.board.floor.contains 77 = false := by decide +kernel
theorem doorAt77 : soko1_2.board.doors.contains 77 = false := by decide +kernel
theorem trapAt77 : soko1_2.board.rollingTraps.contains 77 = false := by decide +kernel
theorem boxAt77 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p 77 = false := rfl
theorem holeAt77 (p : Pattern) : project (soko1_2.initial.holes.drop 1) 77 = false := rfl
theorem advanceAt77_north : advance soko1_2.board 77 .north = some 51 := by decide +kernel
theorem advanceAt77_south : advance soko1_2.board 77 .south = some 103 := by decide +kernel
theorem advanceAt77_east : advance soko1_2.board 77 .east = none := by decide +kernel
theorem advanceAt77_west : advance soko1_2.board 77 .west = some 76 := by decide +kernel
theorem advanceAt77_northEast : advance soko1_2.board 77 .northEast = none := by decide +kernel
theorem advanceAt77_northWest : advance soko1_2.board 77 .northWest = some 50 := by decide +kernel
theorem advanceAt77_southEast : advance soko1_2.board 77 .southEast = none := by decide +kernel
theorem advanceAt77_southWest : advance soko1_2.board 77 .southWest = some 102 := by decide +kernel
theorem floorAt78 : soko1_2.board.floor.contains 78 = false := by decide +kernel
theorem doorAt78 : soko1_2.board.doors.contains 78 = false := by decide +kernel
theorem trapAt78 : soko1_2.board.rollingTraps.contains 78 = false := by decide +kernel
theorem boxAt78 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p 78 = false := rfl
theorem holeAt78 (p : Pattern) : project (soko1_2.initial.holes.drop 1) 78 = false := rfl
theorem advanceAt78_north : advance soko1_2.board 78 .north = some 52 := by decide +kernel
theorem advanceAt78_south : advance soko1_2.board 78 .south = some 104 := by decide +kernel
theorem advanceAt78_east : advance soko1_2.board 78 .east = some 79 := by decide +kernel
theorem advanceAt78_west : advance soko1_2.board 78 .west = none := by decide +kernel
theorem advanceAt78_northEast : advance soko1_2.board 78 .northEast = some 53 := by decide +kernel
theorem advanceAt78_northWest : advance soko1_2.board 78 .northWest = none := by decide +kernel
theorem advanceAt78_southEast : advance soko1_2.board 78 .southEast = some 105 := by decide +kernel
theorem advanceAt78_southWest : advance soko1_2.board 78 .southWest = none := by decide +kernel
theorem floorAt79 : soko1_2.board.floor.contains 79 = false := by decide +kernel
theorem doorAt79 : soko1_2.board.doors.contains 79 = false := by decide +kernel
theorem trapAt79 : soko1_2.board.rollingTraps.contains 79 = false := by decide +kernel
theorem boxAt79 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p 79 = false := rfl
theorem holeAt79 (p : Pattern) : project (soko1_2.initial.holes.drop 1) 79 = false := rfl
theorem advanceAt79_north : advance soko1_2.board 79 .north = some 53 := by decide +kernel
theorem advanceAt79_south : advance soko1_2.board 79 .south = some 105 := by decide +kernel
theorem advanceAt79_east : advance soko1_2.board 79 .east = some 80 := by decide +kernel
theorem advanceAt79_west : advance soko1_2.board 79 .west = some 78 := by decide +kernel
theorem advanceAt79_northEast : advance soko1_2.board 79 .northEast = some 54 := by decide +kernel
theorem advanceAt79_northWest : advance soko1_2.board 79 .northWest = some 52 := by decide +kernel
theorem advanceAt79_southEast : advance soko1_2.board 79 .southEast = some 106 := by decide +kernel
theorem advanceAt79_southWest : advance soko1_2.board 79 .southWest = some 104 := by decide +kernel
end NetHack.Soko12Forward220.Unified.P01
