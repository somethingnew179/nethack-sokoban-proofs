import NetHack.Soko12Forward220.Unified.P02.OracleCells01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P02
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem floorAt80 : soko1_2.board.floor.contains 80 = false := by decide +kernel
theorem doorAt80 : soko1_2.board.doors.contains 80 = false := by decide +kernel
theorem trapAt80 : soko1_2.board.rollingTraps.contains 80 = false := by decide +kernel
theorem boxAt80 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p 80 = false := rfl
theorem holeAt80 (p : Pattern) : project (soko1_2.initial.holes.drop 2) 80 = false := rfl
theorem advanceAt80_north : advance soko1_2.board 80 .north = some 54 := by decide +kernel
theorem advanceAt80_south : advance soko1_2.board 80 .south = some 106 := by decide +kernel
theorem advanceAt80_east : advance soko1_2.board 80 .east = some 81 := by decide +kernel
theorem advanceAt80_west : advance soko1_2.board 80 .west = some 79 := by decide +kernel
theorem advanceAt80_northEast : advance soko1_2.board 80 .northEast = some 55 := by decide +kernel
theorem advanceAt80_northWest : advance soko1_2.board 80 .northWest = some 53 := by decide +kernel
theorem advanceAt80_southEast : advance soko1_2.board 80 .southEast = some 107 := by decide +kernel
theorem advanceAt80_southWest : advance soko1_2.board 80 .southWest = some 105 := by decide +kernel
theorem floorAt81 : soko1_2.board.floor.contains 81 = false := by decide +kernel
theorem doorAt81 : soko1_2.board.doors.contains 81 = false := by decide +kernel
theorem trapAt81 : soko1_2.board.rollingTraps.contains 81 = false := by decide +kernel
theorem boxAt81 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p 81 = false := rfl
theorem holeAt81 (p : Pattern) : project (soko1_2.initial.holes.drop 2) 81 = false := rfl
theorem advanceAt81_north : advance soko1_2.board 81 .north = some 55 := by decide +kernel
theorem advanceAt81_south : advance soko1_2.board 81 .south = some 107 := by decide +kernel
theorem advanceAt81_east : advance soko1_2.board 81 .east = some 82 := by decide +kernel
theorem advanceAt81_west : advance soko1_2.board 81 .west = some 80 := by decide +kernel
theorem advanceAt81_northEast : advance soko1_2.board 81 .northEast = some 56 := by decide +kernel
theorem advanceAt81_northWest : advance soko1_2.board 81 .northWest = some 54 := by decide +kernel
theorem advanceAt81_southEast : advance soko1_2.board 81 .southEast = some 108 := by decide +kernel
theorem advanceAt81_southWest : advance soko1_2.board 81 .southWest = some 106 := by decide +kernel
theorem floorAt82 : soko1_2.board.floor.contains 82 = true := by decide +kernel
theorem doorAt82 : soko1_2.board.doors.contains 82 = false := by decide +kernel
theorem trapAt82 : soko1_2.board.rollingTraps.contains 82 = false := by decide +kernel
theorem boxAt82 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p 82 = p 82 := rfl
theorem holeAt82 (p : Pattern) : project (soko1_2.initial.holes.drop 2) 82 = false := rfl
theorem advanceAt82_north : advance soko1_2.board 82 .north = some 56 := by decide +kernel
theorem advanceAt82_south : advance soko1_2.board 82 .south = some 108 := by decide +kernel
theorem advanceAt82_east : advance soko1_2.board 82 .east = some 83 := by decide +kernel
theorem advanceAt82_west : advance soko1_2.board 82 .west = some 81 := by decide +kernel
theorem advanceAt82_northEast : advance soko1_2.board 82 .northEast = some 57 := by decide +kernel
theorem advanceAt82_northWest : advance soko1_2.board 82 .northWest = some 55 := by decide +kernel
theorem advanceAt82_southEast : advance soko1_2.board 82 .southEast = some 109 := by decide +kernel
theorem advanceAt82_southWest : advance soko1_2.board 82 .southWest = some 107 := by decide +kernel
theorem floorAt83 : soko1_2.board.floor.contains 83 = false := by decide +kernel
theorem doorAt83 : soko1_2.board.doors.contains 83 = false := by decide +kernel
theorem trapAt83 : soko1_2.board.rollingTraps.contains 83 = false := by decide +kernel
theorem boxAt83 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p 83 = false := rfl
theorem holeAt83 (p : Pattern) : project (soko1_2.initial.holes.drop 2) 83 = false := rfl
theorem advanceAt83_north : advance soko1_2.board 83 .north = some 57 := by decide +kernel
theorem advanceAt83_south : advance soko1_2.board 83 .south = some 109 := by decide +kernel
theorem advanceAt83_east : advance soko1_2.board 83 .east = some 84 := by decide +kernel
theorem advanceAt83_west : advance soko1_2.board 83 .west = some 82 := by decide +kernel
theorem advanceAt83_northEast : advance soko1_2.board 83 .northEast = some 58 := by decide +kernel
theorem advanceAt83_northWest : advance soko1_2.board 83 .northWest = some 56 := by decide +kernel
theorem advanceAt83_southEast : advance soko1_2.board 83 .southEast = some 110 := by decide +kernel
theorem advanceAt83_southWest : advance soko1_2.board 83 .southWest = some 108 := by decide +kernel
theorem floorAt84 : soko1_2.board.floor.contains 84 = false := by decide +kernel
theorem doorAt84 : soko1_2.board.doors.contains 84 = false := by decide +kernel
theorem trapAt84 : soko1_2.board.rollingTraps.contains 84 = false := by decide +kernel
theorem boxAt84 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p 84 = false := rfl
theorem holeAt84 (p : Pattern) : project (soko1_2.initial.holes.drop 2) 84 = false := rfl
theorem advanceAt84_north : advance soko1_2.board 84 .north = some 58 := by decide +kernel
theorem advanceAt84_south : advance soko1_2.board 84 .south = some 110 := by decide +kernel
theorem advanceAt84_east : advance soko1_2.board 84 .east = some 85 := by decide +kernel
theorem advanceAt84_west : advance soko1_2.board 84 .west = some 83 := by decide +kernel
theorem advanceAt84_northEast : advance soko1_2.board 84 .northEast = some 59 := by decide +kernel
theorem advanceAt84_northWest : advance soko1_2.board 84 .northWest = some 57 := by decide +kernel
theorem advanceAt84_southEast : advance soko1_2.board 84 .southEast = some 111 := by decide +kernel
theorem advanceAt84_southWest : advance soko1_2.board 84 .southWest = some 109 := by decide +kernel
theorem floorAt85 : soko1_2.board.floor.contains 85 = false := by decide +kernel
theorem doorAt85 : soko1_2.board.doors.contains 85 = false := by decide +kernel
theorem trapAt85 : soko1_2.board.rollingTraps.contains 85 = false := by decide +kernel
theorem boxAt85 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p 85 = false := rfl
theorem holeAt85 (p : Pattern) : project (soko1_2.initial.holes.drop 2) 85 = false := rfl
theorem advanceAt85_north : advance soko1_2.board 85 .north = some 59 := by decide +kernel
theorem advanceAt85_south : advance soko1_2.board 85 .south = some 111 := by decide +kernel
theorem advanceAt85_east : advance soko1_2.board 85 .east = some 86 := by decide +kernel
theorem advanceAt85_west : advance soko1_2.board 85 .west = some 84 := by decide +kernel
theorem advanceAt85_northEast : advance soko1_2.board 85 .northEast = some 60 := by decide +kernel
theorem advanceAt85_northWest : advance soko1_2.board 85 .northWest = some 58 := by decide +kernel
theorem advanceAt85_southEast : advance soko1_2.board 85 .southEast = some 112 := by decide +kernel
theorem advanceAt85_southWest : advance soko1_2.board 85 .southWest = some 110 := by decide +kernel
theorem floorAt86 : soko1_2.board.floor.contains 86 = false := by decide +kernel
theorem doorAt86 : soko1_2.board.doors.contains 86 = false := by decide +kernel
theorem trapAt86 : soko1_2.board.rollingTraps.contains 86 = false := by decide +kernel
theorem boxAt86 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p 86 = false := rfl
theorem holeAt86 (p : Pattern) : project (soko1_2.initial.holes.drop 2) 86 = false := rfl
theorem advanceAt86_north : advance soko1_2.board 86 .north = some 60 := by decide +kernel
theorem advanceAt86_south : advance soko1_2.board 86 .south = some 112 := by decide +kernel
theorem advanceAt86_east : advance soko1_2.board 86 .east = some 87 := by decide +kernel
theorem advanceAt86_west : advance soko1_2.board 86 .west = some 85 := by decide +kernel
theorem advanceAt86_northEast : advance soko1_2.board 86 .northEast = some 61 := by decide +kernel
theorem advanceAt86_northWest : advance soko1_2.board 86 .northWest = some 59 := by decide +kernel
theorem advanceAt86_southEast : advance soko1_2.board 86 .southEast = some 113 := by decide +kernel
theorem advanceAt86_southWest : advance soko1_2.board 86 .southWest = some 111 := by decide +kernel
theorem floorAt87 : soko1_2.board.floor.contains 87 = false := by decide +kernel
theorem doorAt87 : soko1_2.board.doors.contains 87 = false := by decide +kernel
theorem trapAt87 : soko1_2.board.rollingTraps.contains 87 = false := by decide +kernel
theorem boxAt87 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p 87 = false := rfl
theorem holeAt87 (p : Pattern) : project (soko1_2.initial.holes.drop 2) 87 = false := rfl
theorem advanceAt87_north : advance soko1_2.board 87 .north = some 61 := by decide +kernel
theorem advanceAt87_south : advance soko1_2.board 87 .south = some 113 := by decide +kernel
theorem advanceAt87_east : advance soko1_2.board 87 .east = some 88 := by decide +kernel
theorem advanceAt87_west : advance soko1_2.board 87 .west = some 86 := by decide +kernel
theorem advanceAt87_northEast : advance soko1_2.board 87 .northEast = some 62 := by decide +kernel
theorem advanceAt87_northWest : advance soko1_2.board 87 .northWest = some 60 := by decide +kernel
theorem advanceAt87_southEast : advance soko1_2.board 87 .southEast = some 114 := by decide +kernel
theorem advanceAt87_southWest : advance soko1_2.board 87 .southWest = some 112 := by decide +kernel
theorem floorAt88 : soko1_2.board.floor.contains 88 = false := by decide +kernel
theorem doorAt88 : soko1_2.board.doors.contains 88 = false := by decide +kernel
theorem trapAt88 : soko1_2.board.rollingTraps.contains 88 = false := by decide +kernel
theorem boxAt88 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p 88 = false := rfl
theorem holeAt88 (p : Pattern) : project (soko1_2.initial.holes.drop 2) 88 = false := rfl
theorem advanceAt88_north : advance soko1_2.board 88 .north = some 62 := by decide +kernel
theorem advanceAt88_south : advance soko1_2.board 88 .south = some 114 := by decide +kernel
theorem advanceAt88_east : advance soko1_2.board 88 .east = some 89 := by decide +kernel
theorem advanceAt88_west : advance soko1_2.board 88 .west = some 87 := by decide +kernel
theorem advanceAt88_northEast : advance soko1_2.board 88 .northEast = some 63 := by decide +kernel
theorem advanceAt88_northWest : advance soko1_2.board 88 .northWest = some 61 := by decide +kernel
theorem advanceAt88_southEast : advance soko1_2.board 88 .southEast = some 115 := by decide +kernel
theorem advanceAt88_southWest : advance soko1_2.board 88 .southWest = some 113 := by decide +kernel
theorem floorAt89 : soko1_2.board.floor.contains 89 = false := by decide +kernel
theorem doorAt89 : soko1_2.board.doors.contains 89 = false := by decide +kernel
theorem trapAt89 : soko1_2.board.rollingTraps.contains 89 = false := by decide +kernel
theorem boxAt89 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p 89 = false := rfl
theorem holeAt89 (p : Pattern) : project (soko1_2.initial.holes.drop 2) 89 = false := rfl
theorem advanceAt89_north : advance soko1_2.board 89 .north = some 63 := by decide +kernel
theorem advanceAt89_south : advance soko1_2.board 89 .south = some 115 := by decide +kernel
theorem advanceAt89_east : advance soko1_2.board 89 .east = some 90 := by decide +kernel
theorem advanceAt89_west : advance soko1_2.board 89 .west = some 88 := by decide +kernel
theorem advanceAt89_northEast : advance soko1_2.board 89 .northEast = some 64 := by decide +kernel
theorem advanceAt89_northWest : advance soko1_2.board 89 .northWest = some 62 := by decide +kernel
theorem advanceAt89_southEast : advance soko1_2.board 89 .southEast = some 116 := by decide +kernel
theorem advanceAt89_southWest : advance soko1_2.board 89 .southWest = some 114 := by decide +kernel
theorem floorAt90 : soko1_2.board.floor.contains 90 = false := by decide +kernel
theorem doorAt90 : soko1_2.board.doors.contains 90 = false := by decide +kernel
theorem trapAt90 : soko1_2.board.rollingTraps.contains 90 = false := by decide +kernel
theorem boxAt90 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p 90 = false := rfl
theorem holeAt90 (p : Pattern) : project (soko1_2.initial.holes.drop 2) 90 = false := rfl
theorem advanceAt90_north : advance soko1_2.board 90 .north = some 64 := by decide +kernel
theorem advanceAt90_south : advance soko1_2.board 90 .south = some 116 := by decide +kernel
theorem advanceAt90_east : advance soko1_2.board 90 .east = some 91 := by decide +kernel
theorem advanceAt90_west : advance soko1_2.board 90 .west = some 89 := by decide +kernel
theorem advanceAt90_northEast : advance soko1_2.board 90 .northEast = some 65 := by decide +kernel
theorem advanceAt90_northWest : advance soko1_2.board 90 .northWest = some 63 := by decide +kernel
theorem advanceAt90_southEast : advance soko1_2.board 90 .southEast = some 117 := by decide +kernel
theorem advanceAt90_southWest : advance soko1_2.board 90 .southWest = some 115 := by decide +kernel
theorem floorAt91 : soko1_2.board.floor.contains 91 = false := by decide +kernel
theorem doorAt91 : soko1_2.board.doors.contains 91 = false := by decide +kernel
theorem trapAt91 : soko1_2.board.rollingTraps.contains 91 = false := by decide +kernel
theorem boxAt91 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p 91 = false := rfl
theorem holeAt91 (p : Pattern) : project (soko1_2.initial.holes.drop 2) 91 = false := rfl
theorem advanceAt91_north : advance soko1_2.board 91 .north = some 65 := by decide +kernel
theorem advanceAt91_south : advance soko1_2.board 91 .south = some 117 := by decide +kernel
theorem advanceAt91_east : advance soko1_2.board 91 .east = some 92 := by decide +kernel
theorem advanceAt91_west : advance soko1_2.board 91 .west = some 90 := by decide +kernel
theorem advanceAt91_northEast : advance soko1_2.board 91 .northEast = some 66 := by decide +kernel
theorem advanceAt91_northWest : advance soko1_2.board 91 .northWest = some 64 := by decide +kernel
theorem advanceAt91_southEast : advance soko1_2.board 91 .southEast = some 118 := by decide +kernel
theorem advanceAt91_southWest : advance soko1_2.board 91 .southWest = some 116 := by decide +kernel
theorem floorAt92 : soko1_2.board.floor.contains 92 = false := by decide +kernel
theorem doorAt92 : soko1_2.board.doors.contains 92 = false := by decide +kernel
theorem trapAt92 : soko1_2.board.rollingTraps.contains 92 = false := by decide +kernel
theorem boxAt92 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p 92 = false := rfl
theorem holeAt92 (p : Pattern) : project (soko1_2.initial.holes.drop 2) 92 = false := rfl
theorem advanceAt92_north : advance soko1_2.board 92 .north = some 66 := by decide +kernel
theorem advanceAt92_south : advance soko1_2.board 92 .south = some 118 := by decide +kernel
theorem advanceAt92_east : advance soko1_2.board 92 .east = some 93 := by decide +kernel
theorem advanceAt92_west : advance soko1_2.board 92 .west = some 91 := by decide +kernel
theorem advanceAt92_northEast : advance soko1_2.board 92 .northEast = some 67 := by decide +kernel
theorem advanceAt92_northWest : advance soko1_2.board 92 .northWest = some 65 := by decide +kernel
theorem advanceAt92_southEast : advance soko1_2.board 92 .southEast = some 119 := by decide +kernel
theorem advanceAt92_southWest : advance soko1_2.board 92 .southWest = some 117 := by decide +kernel
theorem floorAt93 : soko1_2.board.floor.contains 93 = false := by decide +kernel
theorem doorAt93 : soko1_2.board.doors.contains 93 = false := by decide +kernel
theorem trapAt93 : soko1_2.board.rollingTraps.contains 93 = false := by decide +kernel
theorem boxAt93 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p 93 = false := rfl
theorem holeAt93 (p : Pattern) : project (soko1_2.initial.holes.drop 2) 93 = false := rfl
theorem advanceAt93_north : advance soko1_2.board 93 .north = some 67 := by decide +kernel
theorem advanceAt93_south : advance soko1_2.board 93 .south = some 119 := by decide +kernel
theorem advanceAt93_east : advance soko1_2.board 93 .east = some 94 := by decide +kernel
theorem advanceAt93_west : advance soko1_2.board 93 .west = some 92 := by decide +kernel
theorem advanceAt93_northEast : advance soko1_2.board 93 .northEast = some 68 := by decide +kernel
theorem advanceAt93_northWest : advance soko1_2.board 93 .northWest = some 66 := by decide +kernel
theorem advanceAt93_southEast : advance soko1_2.board 93 .southEast = some 120 := by decide +kernel
theorem advanceAt93_southWest : advance soko1_2.board 93 .southWest = some 118 := by decide +kernel
theorem floorAt94 : soko1_2.board.floor.contains 94 = false := by decide +kernel
theorem doorAt94 : soko1_2.board.doors.contains 94 = false := by decide +kernel
theorem trapAt94 : soko1_2.board.rollingTraps.contains 94 = false := by decide +kernel
theorem boxAt94 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p 94 = false := rfl
theorem holeAt94 (p : Pattern) : project (soko1_2.initial.holes.drop 2) 94 = false := rfl
theorem advanceAt94_north : advance soko1_2.board 94 .north = some 68 := by decide +kernel
theorem advanceAt94_south : advance soko1_2.board 94 .south = some 120 := by decide +kernel
theorem advanceAt94_east : advance soko1_2.board 94 .east = some 95 := by decide +kernel
theorem advanceAt94_west : advance soko1_2.board 94 .west = some 93 := by decide +kernel
theorem advanceAt94_northEast : advance soko1_2.board 94 .northEast = some 69 := by decide +kernel
theorem advanceAt94_northWest : advance soko1_2.board 94 .northWest = some 67 := by decide +kernel
theorem advanceAt94_southEast : advance soko1_2.board 94 .southEast = some 121 := by decide +kernel
theorem advanceAt94_southWest : advance soko1_2.board 94 .southWest = some 119 := by decide +kernel
theorem floorAt95 : soko1_2.board.floor.contains 95 = false := by decide +kernel
theorem doorAt95 : soko1_2.board.doors.contains 95 = false := by decide +kernel
theorem trapAt95 : soko1_2.board.rollingTraps.contains 95 = false := by decide +kernel
theorem boxAt95 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p 95 = false := rfl
theorem holeAt95 (p : Pattern) : project (soko1_2.initial.holes.drop 2) 95 = false := rfl
theorem advanceAt95_north : advance soko1_2.board 95 .north = some 69 := by decide +kernel
theorem advanceAt95_south : advance soko1_2.board 95 .south = some 121 := by decide +kernel
theorem advanceAt95_east : advance soko1_2.board 95 .east = some 96 := by decide +kernel
theorem advanceAt95_west : advance soko1_2.board 95 .west = some 94 := by decide +kernel
theorem advanceAt95_northEast : advance soko1_2.board 95 .northEast = some 70 := by decide +kernel
theorem advanceAt95_northWest : advance soko1_2.board 95 .northWest = some 68 := by decide +kernel
theorem advanceAt95_southEast : advance soko1_2.board 95 .southEast = some 122 := by decide +kernel
theorem advanceAt95_southWest : advance soko1_2.board 95 .southWest = some 120 := by decide +kernel
theorem floorAt96 : soko1_2.board.floor.contains 96 = false := by decide +kernel
theorem doorAt96 : soko1_2.board.doors.contains 96 = false := by decide +kernel
theorem trapAt96 : soko1_2.board.rollingTraps.contains 96 = false := by decide +kernel
theorem boxAt96 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p 96 = false := rfl
theorem holeAt96 (p : Pattern) : project (soko1_2.initial.holes.drop 2) 96 = false := rfl
theorem advanceAt96_north : advance soko1_2.board 96 .north = some 70 := by decide +kernel
theorem advanceAt96_south : advance soko1_2.board 96 .south = some 122 := by decide +kernel
theorem advanceAt96_east : advance soko1_2.board 96 .east = some 97 := by decide +kernel
theorem advanceAt96_west : advance soko1_2.board 96 .west = some 95 := by decide +kernel
theorem advanceAt96_northEast : advance soko1_2.board 96 .northEast = some 71 := by decide +kernel
theorem advanceAt96_northWest : advance soko1_2.board 96 .northWest = some 69 := by decide +kernel
theorem advanceAt96_southEast : advance soko1_2.board 96 .southEast = some 123 := by decide +kernel
theorem advanceAt96_southWest : advance soko1_2.board 96 .southWest = some 121 := by decide +kernel
theorem floorAt97 : soko1_2.board.floor.contains 97 = false := by decide +kernel
theorem doorAt97 : soko1_2.board.doors.contains 97 = false := by decide +kernel
theorem trapAt97 : soko1_2.board.rollingTraps.contains 97 = false := by decide +kernel
theorem boxAt97 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p 97 = false := rfl
theorem holeAt97 (p : Pattern) : project (soko1_2.initial.holes.drop 2) 97 = false := rfl
theorem advanceAt97_north : advance soko1_2.board 97 .north = some 71 := by decide +kernel
theorem advanceAt97_south : advance soko1_2.board 97 .south = some 123 := by decide +kernel
theorem advanceAt97_east : advance soko1_2.board 97 .east = some 98 := by decide +kernel
theorem advanceAt97_west : advance soko1_2.board 97 .west = some 96 := by decide +kernel
theorem advanceAt97_northEast : advance soko1_2.board 97 .northEast = some 72 := by decide +kernel
theorem advanceAt97_northWest : advance soko1_2.board 97 .northWest = some 70 := by decide +kernel
theorem advanceAt97_southEast : advance soko1_2.board 97 .southEast = some 124 := by decide +kernel
theorem advanceAt97_southWest : advance soko1_2.board 97 .southWest = some 122 := by decide +kernel
theorem floorAt98 : soko1_2.board.floor.contains 98 = false := by decide +kernel
theorem doorAt98 : soko1_2.board.doors.contains 98 = false := by decide +kernel
theorem trapAt98 : soko1_2.board.rollingTraps.contains 98 = false := by decide +kernel
theorem boxAt98 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p 98 = false := rfl
theorem holeAt98 (p : Pattern) : project (soko1_2.initial.holes.drop 2) 98 = false := rfl
theorem advanceAt98_north : advance soko1_2.board 98 .north = some 72 := by decide +kernel
theorem advanceAt98_south : advance soko1_2.board 98 .south = some 124 := by decide +kernel
theorem advanceAt98_east : advance soko1_2.board 98 .east = some 99 := by decide +kernel
theorem advanceAt98_west : advance soko1_2.board 98 .west = some 97 := by decide +kernel
theorem advanceAt98_northEast : advance soko1_2.board 98 .northEast = some 73 := by decide +kernel
theorem advanceAt98_northWest : advance soko1_2.board 98 .northWest = some 71 := by decide +kernel
theorem advanceAt98_southEast : advance soko1_2.board 98 .southEast = some 125 := by decide +kernel
theorem advanceAt98_southWest : advance soko1_2.board 98 .southWest = some 123 := by decide +kernel
theorem floorAt99 : soko1_2.board.floor.contains 99 = false := by decide +kernel
theorem doorAt99 : soko1_2.board.doors.contains 99 = false := by decide +kernel
theorem trapAt99 : soko1_2.board.rollingTraps.contains 99 = false := by decide +kernel
theorem boxAt99 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p 99 = false := rfl
theorem holeAt99 (p : Pattern) : project (soko1_2.initial.holes.drop 2) 99 = false := rfl
theorem advanceAt99_north : advance soko1_2.board 99 .north = some 73 := by decide +kernel
theorem advanceAt99_south : advance soko1_2.board 99 .south = some 125 := by decide +kernel
theorem advanceAt99_east : advance soko1_2.board 99 .east = some 100 := by decide +kernel
theorem advanceAt99_west : advance soko1_2.board 99 .west = some 98 := by decide +kernel
theorem advanceAt99_northEast : advance soko1_2.board 99 .northEast = some 74 := by decide +kernel
theorem advanceAt99_northWest : advance soko1_2.board 99 .northWest = some 72 := by decide +kernel
theorem advanceAt99_southEast : advance soko1_2.board 99 .southEast = some 126 := by decide +kernel
theorem advanceAt99_southWest : advance soko1_2.board 99 .southWest = some 124 := by decide +kernel
theorem floorAt100 : soko1_2.board.floor.contains 100 = false := by decide +kernel
theorem doorAt100 : soko1_2.board.doors.contains 100 = false := by decide +kernel
theorem trapAt100 : soko1_2.board.rollingTraps.contains 100 = false := by decide +kernel
theorem boxAt100 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p 100 = false := rfl
theorem holeAt100 (p : Pattern) : project (soko1_2.initial.holes.drop 2) 100 = false := rfl
theorem advanceAt100_north : advance soko1_2.board 100 .north = some 74 := by decide +kernel
theorem advanceAt100_south : advance soko1_2.board 100 .south = some 126 := by decide +kernel
theorem advanceAt100_east : advance soko1_2.board 100 .east = some 101 := by decide +kernel
theorem advanceAt100_west : advance soko1_2.board 100 .west = some 99 := by decide +kernel
theorem advanceAt100_northEast : advance soko1_2.board 100 .northEast = some 75 := by decide +kernel
theorem advanceAt100_northWest : advance soko1_2.board 100 .northWest = some 73 := by decide +kernel
theorem advanceAt100_southEast : advance soko1_2.board 100 .southEast = some 127 := by decide +kernel
theorem advanceAt100_southWest : advance soko1_2.board 100 .southWest = some 125 := by decide +kernel
theorem floorAt101 : soko1_2.board.floor.contains 101 = false := by decide +kernel
theorem doorAt101 : soko1_2.board.doors.contains 101 = false := by decide +kernel
theorem trapAt101 : soko1_2.board.rollingTraps.contains 101 = false := by decide +kernel
theorem boxAt101 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p 101 = false := rfl
theorem holeAt101 (p : Pattern) : project (soko1_2.initial.holes.drop 2) 101 = false := rfl
theorem advanceAt101_north : advance soko1_2.board 101 .north = some 75 := by decide +kernel
theorem advanceAt101_south : advance soko1_2.board 101 .south = some 127 := by decide +kernel
theorem advanceAt101_east : advance soko1_2.board 101 .east = some 102 := by decide +kernel
theorem advanceAt101_west : advance soko1_2.board 101 .west = some 100 := by decide +kernel
theorem advanceAt101_northEast : advance soko1_2.board 101 .northEast = some 76 := by decide +kernel
theorem advanceAt101_northWest : advance soko1_2.board 101 .northWest = some 74 := by decide +kernel
theorem advanceAt101_southEast : advance soko1_2.board 101 .southEast = some 128 := by decide +kernel
theorem advanceAt101_southWest : advance soko1_2.board 101 .southWest = some 126 := by decide +kernel
theorem floorAt102 : soko1_2.board.floor.contains 102 = true := by decide +kernel
theorem doorAt102 : soko1_2.board.doors.contains 102 = false := by decide +kernel
theorem trapAt102 : soko1_2.board.rollingTraps.contains 102 = false := by decide +kernel
theorem boxAt102 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p 102 = false := rfl
theorem holeAt102 (p : Pattern) : project (soko1_2.initial.holes.drop 2) 102 = false := rfl
theorem advanceAt102_north : advance soko1_2.board 102 .north = some 76 := by decide +kernel
theorem advanceAt102_south : advance soko1_2.board 102 .south = some 128 := by decide +kernel
theorem advanceAt102_east : advance soko1_2.board 102 .east = some 103 := by decide +kernel
theorem advanceAt102_west : advance soko1_2.board 102 .west = some 101 := by decide +kernel
theorem advanceAt102_northEast : advance soko1_2.board 102 .northEast = some 77 := by decide +kernel
theorem advanceAt102_northWest : advance soko1_2.board 102 .northWest = some 75 := by decide +kernel
theorem advanceAt102_southEast : advance soko1_2.board 102 .southEast = some 129 := by decide +kernel
theorem advanceAt102_southWest : advance soko1_2.board 102 .southWest = some 127 := by decide +kernel
theorem floorAt103 : soko1_2.board.floor.contains 103 = false := by decide +kernel
theorem doorAt103 : soko1_2.board.doors.contains 103 = false := by decide +kernel
theorem trapAt103 : soko1_2.board.rollingTraps.contains 103 = false := by decide +kernel
theorem boxAt103 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p 103 = false := rfl
theorem holeAt103 (p : Pattern) : project (soko1_2.initial.holes.drop 2) 103 = false := rfl
theorem advanceAt103_north : advance soko1_2.board 103 .north = some 77 := by decide +kernel
theorem advanceAt103_south : advance soko1_2.board 103 .south = some 129 := by decide +kernel
theorem advanceAt103_east : advance soko1_2.board 103 .east = none := by decide +kernel
theorem advanceAt103_west : advance soko1_2.board 103 .west = some 102 := by decide +kernel
theorem advanceAt103_northEast : advance soko1_2.board 103 .northEast = none := by decide +kernel
theorem advanceAt103_northWest : advance soko1_2.board 103 .northWest = some 76 := by decide +kernel
theorem advanceAt103_southEast : advance soko1_2.board 103 .southEast = none := by decide +kernel
theorem advanceAt103_southWest : advance soko1_2.board 103 .southWest = some 128 := by decide +kernel
theorem floorAt104 : soko1_2.board.floor.contains 104 = false := by decide +kernel
theorem doorAt104 : soko1_2.board.doors.contains 104 = false := by decide +kernel
theorem trapAt104 : soko1_2.board.rollingTraps.contains 104 = false := by decide +kernel
theorem boxAt104 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p 104 = false := rfl
theorem holeAt104 (p : Pattern) : project (soko1_2.initial.holes.drop 2) 104 = false := rfl
theorem advanceAt104_north : advance soko1_2.board 104 .north = some 78 := by decide +kernel
theorem advanceAt104_south : advance soko1_2.board 104 .south = some 130 := by decide +kernel
theorem advanceAt104_east : advance soko1_2.board 104 .east = some 105 := by decide +kernel
theorem advanceAt104_west : advance soko1_2.board 104 .west = none := by decide +kernel
theorem advanceAt104_northEast : advance soko1_2.board 104 .northEast = some 79 := by decide +kernel
theorem advanceAt104_northWest : advance soko1_2.board 104 .northWest = none := by decide +kernel
theorem advanceAt104_southEast : advance soko1_2.board 104 .southEast = some 131 := by decide +kernel
theorem advanceAt104_southWest : advance soko1_2.board 104 .southWest = none := by decide +kernel
theorem floorAt105 : soko1_2.board.floor.contains 105 = true := by decide +kernel
theorem doorAt105 : soko1_2.board.doors.contains 105 = false := by decide +kernel
theorem trapAt105 : soko1_2.board.rollingTraps.contains 105 = false := by decide +kernel
theorem boxAt105 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p 105 = p 105 := rfl
theorem holeAt105 (p : Pattern) : project (soko1_2.initial.holes.drop 2) 105 = false := rfl
theorem advanceAt105_north : advance soko1_2.board 105 .north = some 79 := by decide +kernel
theorem advanceAt105_south : advance soko1_2.board 105 .south = some 131 := by decide +kernel
theorem advanceAt105_east : advance soko1_2.board 105 .east = some 106 := by decide +kernel
theorem advanceAt105_west : advance soko1_2.board 105 .west = some 104 := by decide +kernel
theorem advanceAt105_northEast : advance soko1_2.board 105 .northEast = some 80 := by decide +kernel
theorem advanceAt105_northWest : advance soko1_2.board 105 .northWest = some 78 := by decide +kernel
theorem advanceAt105_southEast : advance soko1_2.board 105 .southEast = some 132 := by decide +kernel
theorem advanceAt105_southWest : advance soko1_2.board 105 .southWest = some 130 := by decide +kernel
theorem floorAt106 : soko1_2.board.floor.contains 106 = true := by decide +kernel
theorem doorAt106 : soko1_2.board.doors.contains 106 = false := by decide +kernel
theorem trapAt106 : soko1_2.board.rollingTraps.contains 106 = false := by decide +kernel
theorem boxAt106 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p 106 = p 106 := rfl
theorem holeAt106 (p : Pattern) : project (soko1_2.initial.holes.drop 2) 106 = false := rfl
theorem advanceAt106_north : advance soko1_2.board 106 .north = some 80 := by decide +kernel
theorem advanceAt106_south : advance soko1_2.board 106 .south = some 132 := by decide +kernel
theorem advanceAt106_east : advance soko1_2.board 106 .east = some 107 := by decide +kernel
theorem advanceAt106_west : advance soko1_2.board 106 .west = some 105 := by decide +kernel
theorem advanceAt106_northEast : advance soko1_2.board 106 .northEast = some 81 := by decide +kernel
theorem advanceAt106_northWest : advance soko1_2.board 106 .northWest = some 79 := by decide +kernel
theorem advanceAt106_southEast : advance soko1_2.board 106 .southEast = some 133 := by decide +kernel
theorem advanceAt106_southWest : advance soko1_2.board 106 .southWest = some 131 := by decide +kernel
theorem floorAt107 : soko1_2.board.floor.contains 107 = false := by decide +kernel
theorem doorAt107 : soko1_2.board.doors.contains 107 = false := by decide +kernel
theorem trapAt107 : soko1_2.board.rollingTraps.contains 107 = false := by decide +kernel
theorem boxAt107 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p 107 = false := rfl
theorem holeAt107 (p : Pattern) : project (soko1_2.initial.holes.drop 2) 107 = false := rfl
theorem advanceAt107_north : advance soko1_2.board 107 .north = some 81 := by decide +kernel
theorem advanceAt107_south : advance soko1_2.board 107 .south = some 133 := by decide +kernel
theorem advanceAt107_east : advance soko1_2.board 107 .east = some 108 := by decide +kernel
theorem advanceAt107_west : advance soko1_2.board 107 .west = some 106 := by decide +kernel
theorem advanceAt107_northEast : advance soko1_2.board 107 .northEast = some 82 := by decide +kernel
theorem advanceAt107_northWest : advance soko1_2.board 107 .northWest = some 80 := by decide +kernel
theorem advanceAt107_southEast : advance soko1_2.board 107 .southEast = some 134 := by decide +kernel
theorem advanceAt107_southWest : advance soko1_2.board 107 .southWest = some 132 := by decide +kernel
theorem floorAt108 : soko1_2.board.floor.contains 108 = true := by decide +kernel
theorem doorAt108 : soko1_2.board.doors.contains 108 = false := by decide +kernel
theorem trapAt108 : soko1_2.board.rollingTraps.contains 108 = false := by decide +kernel
theorem boxAt108 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p 108 = p 108 := rfl
theorem holeAt108 (p : Pattern) : project (soko1_2.initial.holes.drop 2) 108 = false := rfl
theorem advanceAt108_north : advance soko1_2.board 108 .north = some 82 := by decide +kernel
theorem advanceAt108_south : advance soko1_2.board 108 .south = some 134 := by decide +kernel
theorem advanceAt108_east : advance soko1_2.board 108 .east = some 109 := by decide +kernel
theorem advanceAt108_west : advance soko1_2.board 108 .west = some 107 := by decide +kernel
theorem advanceAt108_northEast : advance soko1_2.board 108 .northEast = some 83 := by decide +kernel
theorem advanceAt108_northWest : advance soko1_2.board 108 .northWest = some 81 := by decide +kernel
theorem advanceAt108_southEast : advance soko1_2.board 108 .southEast = some 135 := by decide +kernel
theorem advanceAt108_southWest : advance soko1_2.board 108 .southWest = some 133 := by decide +kernel
theorem floorAt109 : soko1_2.board.floor.contains 109 = false := by decide +kernel
theorem doorAt109 : soko1_2.board.doors.contains 109 = false := by decide +kernel
theorem trapAt109 : soko1_2.board.rollingTraps.contains 109 = false := by decide +kernel
theorem boxAt109 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p 109 = false := rfl
theorem holeAt109 (p : Pattern) : project (soko1_2.initial.holes.drop 2) 109 = false := rfl
theorem advanceAt109_north : advance soko1_2.board 109 .north = some 83 := by decide +kernel
theorem advanceAt109_south : advance soko1_2.board 109 .south = some 135 := by decide +kernel
theorem advanceAt109_east : advance soko1_2.board 109 .east = some 110 := by decide +kernel
theorem advanceAt109_west : advance soko1_2.board 109 .west = some 108 := by decide +kernel
theorem advanceAt109_northEast : advance soko1_2.board 109 .northEast = some 84 := by decide +kernel
theorem advanceAt109_northWest : advance soko1_2.board 109 .northWest = some 82 := by decide +kernel
theorem advanceAt109_southEast : advance soko1_2.board 109 .southEast = some 136 := by decide +kernel
theorem advanceAt109_southWest : advance soko1_2.board 109 .southWest = some 134 := by decide +kernel
theorem floorAt110 : soko1_2.board.floor.contains 110 = false := by decide +kernel
theorem doorAt110 : soko1_2.board.doors.contains 110 = false := by decide +kernel
theorem trapAt110 : soko1_2.board.rollingTraps.contains 110 = false := by decide +kernel
theorem boxAt110 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p 110 = false := rfl
theorem holeAt110 (p : Pattern) : project (soko1_2.initial.holes.drop 2) 110 = false := rfl
theorem advanceAt110_north : advance soko1_2.board 110 .north = some 84 := by decide +kernel
theorem advanceAt110_south : advance soko1_2.board 110 .south = some 136 := by decide +kernel
theorem advanceAt110_east : advance soko1_2.board 110 .east = some 111 := by decide +kernel
theorem advanceAt110_west : advance soko1_2.board 110 .west = some 109 := by decide +kernel
theorem advanceAt110_northEast : advance soko1_2.board 110 .northEast = some 85 := by decide +kernel
theorem advanceAt110_northWest : advance soko1_2.board 110 .northWest = some 83 := by decide +kernel
theorem advanceAt110_southEast : advance soko1_2.board 110 .southEast = some 137 := by decide +kernel
theorem advanceAt110_southWest : advance soko1_2.board 110 .southWest = some 135 := by decide +kernel
theorem floorAt111 : soko1_2.board.floor.contains 111 = false := by decide +kernel
theorem doorAt111 : soko1_2.board.doors.contains 111 = false := by decide +kernel
theorem trapAt111 : soko1_2.board.rollingTraps.contains 111 = false := by decide +kernel
theorem boxAt111 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p 111 = false := rfl
theorem holeAt111 (p : Pattern) : project (soko1_2.initial.holes.drop 2) 111 = false := rfl
theorem advanceAt111_north : advance soko1_2.board 111 .north = some 85 := by decide +kernel
theorem advanceAt111_south : advance soko1_2.board 111 .south = some 137 := by decide +kernel
theorem advanceAt111_east : advance soko1_2.board 111 .east = some 112 := by decide +kernel
theorem advanceAt111_west : advance soko1_2.board 111 .west = some 110 := by decide +kernel
theorem advanceAt111_northEast : advance soko1_2.board 111 .northEast = some 86 := by decide +kernel
theorem advanceAt111_northWest : advance soko1_2.board 111 .northWest = some 84 := by decide +kernel
theorem advanceAt111_southEast : advance soko1_2.board 111 .southEast = some 138 := by decide +kernel
theorem advanceAt111_southWest : advance soko1_2.board 111 .southWest = some 136 := by decide +kernel
theorem floorAt112 : soko1_2.board.floor.contains 112 = false := by decide +kernel
theorem doorAt112 : soko1_2.board.doors.contains 112 = false := by decide +kernel
theorem trapAt112 : soko1_2.board.rollingTraps.contains 112 = false := by decide +kernel
theorem boxAt112 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p 112 = false := rfl
theorem holeAt112 (p : Pattern) : project (soko1_2.initial.holes.drop 2) 112 = false := rfl
theorem advanceAt112_north : advance soko1_2.board 112 .north = some 86 := by decide +kernel
theorem advanceAt112_south : advance soko1_2.board 112 .south = some 138 := by decide +kernel
theorem advanceAt112_east : advance soko1_2.board 112 .east = some 113 := by decide +kernel
theorem advanceAt112_west : advance soko1_2.board 112 .west = some 111 := by decide +kernel
theorem advanceAt112_northEast : advance soko1_2.board 112 .northEast = some 87 := by decide +kernel
theorem advanceAt112_northWest : advance soko1_2.board 112 .northWest = some 85 := by decide +kernel
theorem advanceAt112_southEast : advance soko1_2.board 112 .southEast = some 139 := by decide +kernel
theorem advanceAt112_southWest : advance soko1_2.board 112 .southWest = some 137 := by decide +kernel
theorem floorAt113 : soko1_2.board.floor.contains 113 = false := by decide +kernel
theorem doorAt113 : soko1_2.board.doors.contains 113 = false := by decide +kernel
theorem trapAt113 : soko1_2.board.rollingTraps.contains 113 = false := by decide +kernel
theorem boxAt113 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p 113 = false := rfl
theorem holeAt113 (p : Pattern) : project (soko1_2.initial.holes.drop 2) 113 = false := rfl
theorem advanceAt113_north : advance soko1_2.board 113 .north = some 87 := by decide +kernel
theorem advanceAt113_south : advance soko1_2.board 113 .south = some 139 := by decide +kernel
theorem advanceAt113_east : advance soko1_2.board 113 .east = some 114 := by decide +kernel
theorem advanceAt113_west : advance soko1_2.board 113 .west = some 112 := by decide +kernel
theorem advanceAt113_northEast : advance soko1_2.board 113 .northEast = some 88 := by decide +kernel
theorem advanceAt113_northWest : advance soko1_2.board 113 .northWest = some 86 := by decide +kernel
theorem advanceAt113_southEast : advance soko1_2.board 113 .southEast = some 140 := by decide +kernel
theorem advanceAt113_southWest : advance soko1_2.board 113 .southWest = some 138 := by decide +kernel
theorem floorAt114 : soko1_2.board.floor.contains 114 = false := by decide +kernel
theorem doorAt114 : soko1_2.board.doors.contains 114 = false := by decide +kernel
theorem trapAt114 : soko1_2.board.rollingTraps.contains 114 = false := by decide +kernel
theorem boxAt114 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p 114 = false := rfl
theorem holeAt114 (p : Pattern) : project (soko1_2.initial.holes.drop 2) 114 = false := rfl
theorem advanceAt114_north : advance soko1_2.board 114 .north = some 88 := by decide +kernel
theorem advanceAt114_south : advance soko1_2.board 114 .south = some 140 := by decide +kernel
theorem advanceAt114_east : advance soko1_2.board 114 .east = some 115 := by decide +kernel
theorem advanceAt114_west : advance soko1_2.board 114 .west = some 113 := by decide +kernel
theorem advanceAt114_northEast : advance soko1_2.board 114 .northEast = some 89 := by decide +kernel
theorem advanceAt114_northWest : advance soko1_2.board 114 .northWest = some 87 := by decide +kernel
theorem advanceAt114_southEast : advance soko1_2.board 114 .southEast = some 141 := by decide +kernel
theorem advanceAt114_southWest : advance soko1_2.board 114 .southWest = some 139 := by decide +kernel
theorem floorAt115 : soko1_2.board.floor.contains 115 = true := by decide +kernel
theorem doorAt115 : soko1_2.board.doors.contains 115 = false := by decide +kernel
theorem trapAt115 : soko1_2.board.rollingTraps.contains 115 = false := by decide +kernel
theorem boxAt115 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p 115 = p 115 := rfl
theorem holeAt115 (p : Pattern) : project (soko1_2.initial.holes.drop 2) 115 = false := rfl
theorem advanceAt115_north : advance soko1_2.board 115 .north = some 89 := by decide +kernel
theorem advanceAt115_south : advance soko1_2.board 115 .south = some 141 := by decide +kernel
theorem advanceAt115_east : advance soko1_2.board 115 .east = some 116 := by decide +kernel
theorem advanceAt115_west : advance soko1_2.board 115 .west = some 114 := by decide +kernel
theorem advanceAt115_northEast : advance soko1_2.board 115 .northEast = some 90 := by decide +kernel
theorem advanceAt115_northWest : advance soko1_2.board 115 .northWest = some 88 := by decide +kernel
theorem advanceAt115_southEast : advance soko1_2.board 115 .southEast = some 142 := by decide +kernel
theorem advanceAt115_southWest : advance soko1_2.board 115 .southWest = some 140 := by decide +kernel
theorem floorAt116 : soko1_2.board.floor.contains 116 = true := by decide +kernel
theorem doorAt116 : soko1_2.board.doors.contains 116 = false := by decide +kernel
theorem trapAt116 : soko1_2.board.rollingTraps.contains 116 = false := by decide +kernel
theorem boxAt116 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p 116 = p 116 := rfl
theorem holeAt116 (p : Pattern) : project (soko1_2.initial.holes.drop 2) 116 = false := rfl
theorem advanceAt116_north : advance soko1_2.board 116 .north = some 90 := by decide +kernel
theorem advanceAt116_south : advance soko1_2.board 116 .south = some 142 := by decide +kernel
theorem advanceAt116_east : advance soko1_2.board 116 .east = some 117 := by decide +kernel
theorem advanceAt116_west : advance soko1_2.board 116 .west = some 115 := by decide +kernel
theorem advanceAt116_northEast : advance soko1_2.board 116 .northEast = some 91 := by decide +kernel
theorem advanceAt116_northWest : advance soko1_2.board 116 .northWest = some 89 := by decide +kernel
theorem advanceAt116_southEast : advance soko1_2.board 116 .southEast = some 143 := by decide +kernel
theorem advanceAt116_southWest : advance soko1_2.board 116 .southWest = some 141 := by decide +kernel
theorem floorAt117 : soko1_2.board.floor.contains 117 = true := by decide +kernel
theorem doorAt117 : soko1_2.board.doors.contains 117 = false := by decide +kernel
theorem trapAt117 : soko1_2.board.rollingTraps.contains 117 = false := by decide +kernel
theorem boxAt117 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p 117 = p 117 := rfl
theorem holeAt117 (p : Pattern) : project (soko1_2.initial.holes.drop 2) 117 = false := rfl
theorem advanceAt117_north : advance soko1_2.board 117 .north = some 91 := by decide +kernel
theorem advanceAt117_south : advance soko1_2.board 117 .south = some 143 := by decide +kernel
theorem advanceAt117_east : advance soko1_2.board 117 .east = some 118 := by decide +kernel
theorem advanceAt117_west : advance soko1_2.board 117 .west = some 116 := by decide +kernel
theorem advanceAt117_northEast : advance soko1_2.board 117 .northEast = some 92 := by decide +kernel
theorem advanceAt117_northWest : advance soko1_2.board 117 .northWest = some 90 := by decide +kernel
theorem advanceAt117_southEast : advance soko1_2.board 117 .southEast = some 144 := by decide +kernel
theorem advanceAt117_southWest : advance soko1_2.board 117 .southWest = some 142 := by decide +kernel
theorem floorAt118 : soko1_2.board.floor.contains 118 = false := by decide +kernel
theorem doorAt118 : soko1_2.board.doors.contains 118 = false := by decide +kernel
theorem trapAt118 : soko1_2.board.rollingTraps.contains 118 = false := by decide +kernel
theorem boxAt118 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p 118 = false := rfl
theorem holeAt118 (p : Pattern) : project (soko1_2.initial.holes.drop 2) 118 = false := rfl
theorem advanceAt118_north : advance soko1_2.board 118 .north = some 92 := by decide +kernel
theorem advanceAt118_south : advance soko1_2.board 118 .south = some 144 := by decide +kernel
theorem advanceAt118_east : advance soko1_2.board 118 .east = some 119 := by decide +kernel
theorem advanceAt118_west : advance soko1_2.board 118 .west = some 117 := by decide +kernel
theorem advanceAt118_northEast : advance soko1_2.board 118 .northEast = some 93 := by decide +kernel
theorem advanceAt118_northWest : advance soko1_2.board 118 .northWest = some 91 := by decide +kernel
theorem advanceAt118_southEast : advance soko1_2.board 118 .southEast = some 145 := by decide +kernel
theorem advanceAt118_southWest : advance soko1_2.board 118 .southWest = some 143 := by decide +kernel
theorem floorAt119 : soko1_2.board.floor.contains 119 = false := by decide +kernel
theorem doorAt119 : soko1_2.board.doors.contains 119 = false := by decide +kernel
theorem trapAt119 : soko1_2.board.rollingTraps.contains 119 = false := by decide +kernel
theorem boxAt119 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p 119 = false := rfl
theorem holeAt119 (p : Pattern) : project (soko1_2.initial.holes.drop 2) 119 = false := rfl
theorem advanceAt119_north : advance soko1_2.board 119 .north = some 93 := by decide +kernel
theorem advanceAt119_south : advance soko1_2.board 119 .south = some 145 := by decide +kernel
theorem advanceAt119_east : advance soko1_2.board 119 .east = some 120 := by decide +kernel
theorem advanceAt119_west : advance soko1_2.board 119 .west = some 118 := by decide +kernel
theorem advanceAt119_northEast : advance soko1_2.board 119 .northEast = some 94 := by decide +kernel
theorem advanceAt119_northWest : advance soko1_2.board 119 .northWest = some 92 := by decide +kernel
theorem advanceAt119_southEast : advance soko1_2.board 119 .southEast = some 146 := by decide +kernel
theorem advanceAt119_southWest : advance soko1_2.board 119 .southWest = some 144 := by decide +kernel
end NetHack.Soko12Forward220.Unified.P02
