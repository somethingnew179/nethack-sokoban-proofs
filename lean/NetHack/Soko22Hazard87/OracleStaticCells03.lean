import NetHack.Soko22Hazard87.OracleStaticCells02
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem floorAt120 : soko2_2.board.floor.contains 120 = true := by decide +kernel
theorem doorAt120 : soko2_2.board.doors.contains 120 = false := by decide +kernel
theorem trapAt120 : soko2_2.board.rollingTraps.contains 120 = false := by decide +kernel
theorem boxAt120 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 120 = p 120 := rfl
theorem holeAt120 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 120 = false := rfl
theorem advanceAt120_north : advance soko2_2.board 120 .north = some 98 := by decide +kernel
theorem advanceAt120_south : advance soko2_2.board 120 .south = some 142 := by decide +kernel
theorem advanceAt120_east : advance soko2_2.board 120 .east = some 121 := by decide +kernel
theorem advanceAt120_west : advance soko2_2.board 120 .west = some 119 := by decide +kernel
theorem advanceAt120_northEast : advance soko2_2.board 120 .northEast = some 99 := by decide +kernel
theorem advanceAt120_northWest : advance soko2_2.board 120 .northWest = some 97 := by decide +kernel
theorem advanceAt120_southEast : advance soko2_2.board 120 .southEast = some 143 := by decide +kernel
theorem advanceAt120_southWest : advance soko2_2.board 120 .southWest = some 141 := by decide +kernel
theorem floorAt121 : soko2_2.board.floor.contains 121 = false := by decide +kernel
theorem doorAt121 : soko2_2.board.doors.contains 121 = false := by decide +kernel
theorem trapAt121 : soko2_2.board.rollingTraps.contains 121 = false := by decide +kernel
theorem boxAt121 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 121 = false := rfl
theorem holeAt121 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 121 = false := rfl
theorem advanceAt121_north : advance soko2_2.board 121 .north = some 99 := by decide +kernel
theorem advanceAt121_south : advance soko2_2.board 121 .south = some 143 := by decide +kernel
theorem advanceAt121_east : advance soko2_2.board 121 .east = some 122 := by decide +kernel
theorem advanceAt121_west : advance soko2_2.board 121 .west = some 120 := by decide +kernel
theorem advanceAt121_northEast : advance soko2_2.board 121 .northEast = some 100 := by decide +kernel
theorem advanceAt121_northWest : advance soko2_2.board 121 .northWest = some 98 := by decide +kernel
theorem advanceAt121_southEast : advance soko2_2.board 121 .southEast = some 144 := by decide +kernel
theorem advanceAt121_southWest : advance soko2_2.board 121 .southWest = some 142 := by decide +kernel
theorem floorAt122 : soko2_2.board.floor.contains 122 = true := by decide +kernel
theorem doorAt122 : soko2_2.board.doors.contains 122 = false := by decide +kernel
theorem trapAt122 : soko2_2.board.rollingTraps.contains 122 = false := by decide +kernel
theorem boxAt122 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 122 = false := rfl
theorem holeAt122 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 122 = false := rfl
theorem advanceAt122_north : advance soko2_2.board 122 .north = some 100 := by decide +kernel
theorem advanceAt122_south : advance soko2_2.board 122 .south = some 144 := by decide +kernel
theorem advanceAt122_east : advance soko2_2.board 122 .east = some 123 := by decide +kernel
theorem advanceAt122_west : advance soko2_2.board 122 .west = some 121 := by decide +kernel
theorem advanceAt122_northEast : advance soko2_2.board 122 .northEast = some 101 := by decide +kernel
theorem advanceAt122_northWest : advance soko2_2.board 122 .northWest = some 99 := by decide +kernel
theorem advanceAt122_southEast : advance soko2_2.board 122 .southEast = some 145 := by decide +kernel
theorem advanceAt122_southWest : advance soko2_2.board 122 .southWest = some 143 := by decide +kernel
theorem floorAt123 : soko2_2.board.floor.contains 123 = true := by decide +kernel
theorem doorAt123 : soko2_2.board.doors.contains 123 = false := by decide +kernel
theorem trapAt123 : soko2_2.board.rollingTraps.contains 123 = false := by decide +kernel
theorem boxAt123 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 123 = false := rfl
theorem holeAt123 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 123 = false := rfl
theorem advanceAt123_north : advance soko2_2.board 123 .north = some 101 := by decide +kernel
theorem advanceAt123_south : advance soko2_2.board 123 .south = some 145 := by decide +kernel
theorem advanceAt123_east : advance soko2_2.board 123 .east = some 124 := by decide +kernel
theorem advanceAt123_west : advance soko2_2.board 123 .west = some 122 := by decide +kernel
theorem advanceAt123_northEast : advance soko2_2.board 123 .northEast = some 102 := by decide +kernel
theorem advanceAt123_northWest : advance soko2_2.board 123 .northWest = some 100 := by decide +kernel
theorem advanceAt123_southEast : advance soko2_2.board 123 .southEast = some 146 := by decide +kernel
theorem advanceAt123_southWest : advance soko2_2.board 123 .southWest = some 144 := by decide +kernel
theorem floorAt124 : soko2_2.board.floor.contains 124 = true := by decide +kernel
theorem doorAt124 : soko2_2.board.doors.contains 124 = false := by decide +kernel
theorem trapAt124 : soko2_2.board.rollingTraps.contains 124 = false := by decide +kernel
theorem boxAt124 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 124 = false := rfl
theorem holeAt124 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 124 = false := rfl
theorem advanceAt124_north : advance soko2_2.board 124 .north = some 102 := by decide +kernel
theorem advanceAt124_south : advance soko2_2.board 124 .south = some 146 := by decide +kernel
theorem advanceAt124_east : advance soko2_2.board 124 .east = some 125 := by decide +kernel
theorem advanceAt124_west : advance soko2_2.board 124 .west = some 123 := by decide +kernel
theorem advanceAt124_northEast : advance soko2_2.board 124 .northEast = some 103 := by decide +kernel
theorem advanceAt124_northWest : advance soko2_2.board 124 .northWest = some 101 := by decide +kernel
theorem advanceAt124_southEast : advance soko2_2.board 124 .southEast = some 147 := by decide +kernel
theorem advanceAt124_southWest : advance soko2_2.board 124 .southWest = some 145 := by decide +kernel
theorem floorAt125 : soko2_2.board.floor.contains 125 = true := by decide +kernel
theorem doorAt125 : soko2_2.board.doors.contains 125 = false := by decide +kernel
theorem trapAt125 : soko2_2.board.rollingTraps.contains 125 = false := by decide +kernel
theorem boxAt125 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 125 = false := rfl
theorem holeAt125 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 125 = false := rfl
theorem advanceAt125_north : advance soko2_2.board 125 .north = some 103 := by decide +kernel
theorem advanceAt125_south : advance soko2_2.board 125 .south = some 147 := by decide +kernel
theorem advanceAt125_east : advance soko2_2.board 125 .east = some 126 := by decide +kernel
theorem advanceAt125_west : advance soko2_2.board 125 .west = some 124 := by decide +kernel
theorem advanceAt125_northEast : advance soko2_2.board 125 .northEast = some 104 := by decide +kernel
theorem advanceAt125_northWest : advance soko2_2.board 125 .northWest = some 102 := by decide +kernel
theorem advanceAt125_southEast : advance soko2_2.board 125 .southEast = some 148 := by decide +kernel
theorem advanceAt125_southWest : advance soko2_2.board 125 .southWest = some 146 := by decide +kernel
theorem floorAt126 : soko2_2.board.floor.contains 126 = true := by decide +kernel
theorem doorAt126 : soko2_2.board.doors.contains 126 = false := by decide +kernel
theorem trapAt126 : soko2_2.board.rollingTraps.contains 126 = false := by decide +kernel
theorem boxAt126 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 126 = false := rfl
theorem holeAt126 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 126 = false := rfl
theorem advanceAt126_north : advance soko2_2.board 126 .north = some 104 := by decide +kernel
theorem advanceAt126_south : advance soko2_2.board 126 .south = some 148 := by decide +kernel
theorem advanceAt126_east : advance soko2_2.board 126 .east = some 127 := by decide +kernel
theorem advanceAt126_west : advance soko2_2.board 126 .west = some 125 := by decide +kernel
theorem advanceAt126_northEast : advance soko2_2.board 126 .northEast = some 105 := by decide +kernel
theorem advanceAt126_northWest : advance soko2_2.board 126 .northWest = some 103 := by decide +kernel
theorem advanceAt126_southEast : advance soko2_2.board 126 .southEast = some 149 := by decide +kernel
theorem advanceAt126_southWest : advance soko2_2.board 126 .southWest = some 147 := by decide +kernel
theorem floorAt127 : soko2_2.board.floor.contains 127 = true := by decide +kernel
theorem doorAt127 : soko2_2.board.doors.contains 127 = false := by decide +kernel
theorem trapAt127 : soko2_2.board.rollingTraps.contains 127 = false := by decide +kernel
theorem boxAt127 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 127 = false := rfl
theorem holeAt127 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 127 = false := rfl
theorem advanceAt127_north : advance soko2_2.board 127 .north = some 105 := by decide +kernel
theorem advanceAt127_south : advance soko2_2.board 127 .south = some 149 := by decide +kernel
theorem advanceAt127_east : advance soko2_2.board 127 .east = some 128 := by decide +kernel
theorem advanceAt127_west : advance soko2_2.board 127 .west = some 126 := by decide +kernel
theorem advanceAt127_northEast : advance soko2_2.board 127 .northEast = some 106 := by decide +kernel
theorem advanceAt127_northWest : advance soko2_2.board 127 .northWest = some 104 := by decide +kernel
theorem advanceAt127_southEast : advance soko2_2.board 127 .southEast = some 150 := by decide +kernel
theorem advanceAt127_southWest : advance soko2_2.board 127 .southWest = some 148 := by decide +kernel
theorem floorAt128 : soko2_2.board.floor.contains 128 = true := by decide +kernel
theorem doorAt128 : soko2_2.board.doors.contains 128 = false := by decide +kernel
theorem trapAt128 : soko2_2.board.rollingTraps.contains 128 = false := by decide +kernel
theorem boxAt128 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 128 = false := rfl
theorem holeAt128 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 128 = false := rfl
theorem advanceAt128_north : advance soko2_2.board 128 .north = some 106 := by decide +kernel
theorem advanceAt128_south : advance soko2_2.board 128 .south = some 150 := by decide +kernel
theorem advanceAt128_east : advance soko2_2.board 128 .east = some 129 := by decide +kernel
theorem advanceAt128_west : advance soko2_2.board 128 .west = some 127 := by decide +kernel
theorem advanceAt128_northEast : advance soko2_2.board 128 .northEast = some 107 := by decide +kernel
theorem advanceAt128_northWest : advance soko2_2.board 128 .northWest = some 105 := by decide +kernel
theorem advanceAt128_southEast : advance soko2_2.board 128 .southEast = some 151 := by decide +kernel
theorem advanceAt128_southWest : advance soko2_2.board 128 .southWest = some 149 := by decide +kernel
theorem floorAt129 : soko2_2.board.floor.contains 129 = false := by decide +kernel
theorem doorAt129 : soko2_2.board.doors.contains 129 = false := by decide +kernel
theorem trapAt129 : soko2_2.board.rollingTraps.contains 129 = false := by decide +kernel
theorem boxAt129 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 129 = false := rfl
theorem holeAt129 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 129 = false := rfl
theorem advanceAt129_north : advance soko2_2.board 129 .north = some 107 := by decide +kernel
theorem advanceAt129_south : advance soko2_2.board 129 .south = some 151 := by decide +kernel
theorem advanceAt129_east : advance soko2_2.board 129 .east = some 130 := by decide +kernel
theorem advanceAt129_west : advance soko2_2.board 129 .west = some 128 := by decide +kernel
theorem advanceAt129_northEast : advance soko2_2.board 129 .northEast = some 108 := by decide +kernel
theorem advanceAt129_northWest : advance soko2_2.board 129 .northWest = some 106 := by decide +kernel
theorem advanceAt129_southEast : advance soko2_2.board 129 .southEast = some 152 := by decide +kernel
theorem advanceAt129_southWest : advance soko2_2.board 129 .southWest = some 150 := by decide +kernel
theorem floorAt130 : soko2_2.board.floor.contains 130 = false := by decide +kernel
theorem doorAt130 : soko2_2.board.doors.contains 130 = false := by decide +kernel
theorem trapAt130 : soko2_2.board.rollingTraps.contains 130 = false := by decide +kernel
theorem boxAt130 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 130 = false := rfl
theorem holeAt130 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 130 = false := rfl
theorem advanceAt130_north : advance soko2_2.board 130 .north = some 108 := by decide +kernel
theorem advanceAt130_south : advance soko2_2.board 130 .south = some 152 := by decide +kernel
theorem advanceAt130_east : advance soko2_2.board 130 .east = some 131 := by decide +kernel
theorem advanceAt130_west : advance soko2_2.board 130 .west = some 129 := by decide +kernel
theorem advanceAt130_northEast : advance soko2_2.board 130 .northEast = some 109 := by decide +kernel
theorem advanceAt130_northWest : advance soko2_2.board 130 .northWest = some 107 := by decide +kernel
theorem advanceAt130_southEast : advance soko2_2.board 130 .southEast = some 153 := by decide +kernel
theorem advanceAt130_southWest : advance soko2_2.board 130 .southWest = some 151 := by decide +kernel
theorem floorAt131 : soko2_2.board.floor.contains 131 = false := by decide +kernel
theorem doorAt131 : soko2_2.board.doors.contains 131 = false := by decide +kernel
theorem trapAt131 : soko2_2.board.rollingTraps.contains 131 = false := by decide +kernel
theorem boxAt131 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 131 = false := rfl
theorem holeAt131 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 131 = false := rfl
theorem advanceAt131_north : advance soko2_2.board 131 .north = some 109 := by decide +kernel
theorem advanceAt131_south : advance soko2_2.board 131 .south = some 153 := by decide +kernel
theorem advanceAt131_east : advance soko2_2.board 131 .east = none := by decide +kernel
theorem advanceAt131_west : advance soko2_2.board 131 .west = some 130 := by decide +kernel
theorem advanceAt131_northEast : advance soko2_2.board 131 .northEast = none := by decide +kernel
theorem advanceAt131_northWest : advance soko2_2.board 131 .northWest = some 108 := by decide +kernel
theorem advanceAt131_southEast : advance soko2_2.board 131 .southEast = none := by decide +kernel
theorem advanceAt131_southWest : advance soko2_2.board 131 .southWest = some 152 := by decide +kernel
theorem floorAt132 : soko2_2.board.floor.contains 132 = false := by decide +kernel
theorem doorAt132 : soko2_2.board.doors.contains 132 = false := by decide +kernel
theorem trapAt132 : soko2_2.board.rollingTraps.contains 132 = false := by decide +kernel
theorem boxAt132 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 132 = false := rfl
theorem holeAt132 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 132 = false := rfl
theorem advanceAt132_north : advance soko2_2.board 132 .north = some 110 := by decide +kernel
theorem advanceAt132_south : advance soko2_2.board 132 .south = some 154 := by decide +kernel
theorem advanceAt132_east : advance soko2_2.board 132 .east = some 133 := by decide +kernel
theorem advanceAt132_west : advance soko2_2.board 132 .west = none := by decide +kernel
theorem advanceAt132_northEast : advance soko2_2.board 132 .northEast = some 111 := by decide +kernel
theorem advanceAt132_northWest : advance soko2_2.board 132 .northWest = none := by decide +kernel
theorem advanceAt132_southEast : advance soko2_2.board 132 .southEast = some 155 := by decide +kernel
theorem advanceAt132_southWest : advance soko2_2.board 132 .southWest = none := by decide +kernel
theorem floorAt133 : soko2_2.board.floor.contains 133 = true := by decide +kernel
theorem doorAt133 : soko2_2.board.doors.contains 133 = false := by decide +kernel
theorem trapAt133 : soko2_2.board.rollingTraps.contains 133 = false := by decide +kernel
theorem boxAt133 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 133 = p 133 := rfl
theorem holeAt133 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 133 = false := rfl
theorem advanceAt133_north : advance soko2_2.board 133 .north = some 111 := by decide +kernel
theorem advanceAt133_south : advance soko2_2.board 133 .south = some 155 := by decide +kernel
theorem advanceAt133_east : advance soko2_2.board 133 .east = some 134 := by decide +kernel
theorem advanceAt133_west : advance soko2_2.board 133 .west = some 132 := by decide +kernel
theorem advanceAt133_northEast : advance soko2_2.board 133 .northEast = some 112 := by decide +kernel
theorem advanceAt133_northWest : advance soko2_2.board 133 .northWest = some 110 := by decide +kernel
theorem advanceAt133_southEast : advance soko2_2.board 133 .southEast = some 156 := by decide +kernel
theorem advanceAt133_southWest : advance soko2_2.board 133 .southWest = some 154 := by decide +kernel
theorem floorAt134 : soko2_2.board.floor.contains 134 = true := by decide +kernel
theorem doorAt134 : soko2_2.board.doors.contains 134 = false := by decide +kernel
theorem trapAt134 : soko2_2.board.rollingTraps.contains 134 = false := by decide +kernel
theorem boxAt134 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 134 = p 134 := rfl
theorem holeAt134 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 134 = false := rfl
theorem advanceAt134_north : advance soko2_2.board 134 .north = some 112 := by decide +kernel
theorem advanceAt134_south : advance soko2_2.board 134 .south = some 156 := by decide +kernel
theorem advanceAt134_east : advance soko2_2.board 134 .east = some 135 := by decide +kernel
theorem advanceAt134_west : advance soko2_2.board 134 .west = some 133 := by decide +kernel
theorem advanceAt134_northEast : advance soko2_2.board 134 .northEast = some 113 := by decide +kernel
theorem advanceAt134_northWest : advance soko2_2.board 134 .northWest = some 111 := by decide +kernel
theorem advanceAt134_southEast : advance soko2_2.board 134 .southEast = some 157 := by decide +kernel
theorem advanceAt134_southWest : advance soko2_2.board 134 .southWest = some 155 := by decide +kernel
theorem floorAt135 : soko2_2.board.floor.contains 135 = true := by decide +kernel
theorem doorAt135 : soko2_2.board.doors.contains 135 = false := by decide +kernel
theorem trapAt135 : soko2_2.board.rollingTraps.contains 135 = false := by decide +kernel
theorem boxAt135 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 135 = p 135 := rfl
theorem holeAt135 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 135 = false := rfl
theorem advanceAt135_north : advance soko2_2.board 135 .north = some 113 := by decide +kernel
theorem advanceAt135_south : advance soko2_2.board 135 .south = some 157 := by decide +kernel
theorem advanceAt135_east : advance soko2_2.board 135 .east = some 136 := by decide +kernel
theorem advanceAt135_west : advance soko2_2.board 135 .west = some 134 := by decide +kernel
theorem advanceAt135_northEast : advance soko2_2.board 135 .northEast = some 114 := by decide +kernel
theorem advanceAt135_northWest : advance soko2_2.board 135 .northWest = some 112 := by decide +kernel
theorem advanceAt135_southEast : advance soko2_2.board 135 .southEast = some 158 := by decide +kernel
theorem advanceAt135_southWest : advance soko2_2.board 135 .southWest = some 156 := by decide +kernel
theorem floorAt136 : soko2_2.board.floor.contains 136 = true := by decide +kernel
theorem doorAt136 : soko2_2.board.doors.contains 136 = false := by decide +kernel
theorem trapAt136 : soko2_2.board.rollingTraps.contains 136 = false := by decide +kernel
theorem boxAt136 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 136 = p 136 := rfl
theorem holeAt136 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 136 = false := rfl
theorem advanceAt136_north : advance soko2_2.board 136 .north = some 114 := by decide +kernel
theorem advanceAt136_south : advance soko2_2.board 136 .south = some 158 := by decide +kernel
theorem advanceAt136_east : advance soko2_2.board 136 .east = some 137 := by decide +kernel
theorem advanceAt136_west : advance soko2_2.board 136 .west = some 135 := by decide +kernel
theorem advanceAt136_northEast : advance soko2_2.board 136 .northEast = some 115 := by decide +kernel
theorem advanceAt136_northWest : advance soko2_2.board 136 .northWest = some 113 := by decide +kernel
theorem advanceAt136_southEast : advance soko2_2.board 136 .southEast = some 159 := by decide +kernel
theorem advanceAt136_southWest : advance soko2_2.board 136 .southWest = some 157 := by decide +kernel
theorem floorAt137 : soko2_2.board.floor.contains 137 = false := by decide +kernel
theorem doorAt137 : soko2_2.board.doors.contains 137 = false := by decide +kernel
theorem trapAt137 : soko2_2.board.rollingTraps.contains 137 = false := by decide +kernel
theorem boxAt137 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 137 = false := rfl
theorem holeAt137 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 137 = false := rfl
theorem advanceAt137_north : advance soko2_2.board 137 .north = some 115 := by decide +kernel
theorem advanceAt137_south : advance soko2_2.board 137 .south = some 159 := by decide +kernel
theorem advanceAt137_east : advance soko2_2.board 137 .east = some 138 := by decide +kernel
theorem advanceAt137_west : advance soko2_2.board 137 .west = some 136 := by decide +kernel
theorem advanceAt137_northEast : advance soko2_2.board 137 .northEast = some 116 := by decide +kernel
theorem advanceAt137_northWest : advance soko2_2.board 137 .northWest = some 114 := by decide +kernel
theorem advanceAt137_southEast : advance soko2_2.board 137 .southEast = some 160 := by decide +kernel
theorem advanceAt137_southWest : advance soko2_2.board 137 .southWest = some 158 := by decide +kernel
theorem floorAt138 : soko2_2.board.floor.contains 138 = true := by decide +kernel
theorem doorAt138 : soko2_2.board.doors.contains 138 = false := by decide +kernel
theorem trapAt138 : soko2_2.board.rollingTraps.contains 138 = false := by decide +kernel
theorem boxAt138 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 138 = p 138 := rfl
theorem holeAt138 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 138 = false := rfl
theorem advanceAt138_north : advance soko2_2.board 138 .north = some 116 := by decide +kernel
theorem advanceAt138_south : advance soko2_2.board 138 .south = some 160 := by decide +kernel
theorem advanceAt138_east : advance soko2_2.board 138 .east = some 139 := by decide +kernel
theorem advanceAt138_west : advance soko2_2.board 138 .west = some 137 := by decide +kernel
theorem advanceAt138_northEast : advance soko2_2.board 138 .northEast = some 117 := by decide +kernel
theorem advanceAt138_northWest : advance soko2_2.board 138 .northWest = some 115 := by decide +kernel
theorem advanceAt138_southEast : advance soko2_2.board 138 .southEast = some 161 := by decide +kernel
theorem advanceAt138_southWest : advance soko2_2.board 138 .southWest = some 159 := by decide +kernel
theorem floorAt139 : soko2_2.board.floor.contains 139 = false := by decide +kernel
theorem doorAt139 : soko2_2.board.doors.contains 139 = false := by decide +kernel
theorem trapAt139 : soko2_2.board.rollingTraps.contains 139 = false := by decide +kernel
theorem boxAt139 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 139 = false := rfl
theorem holeAt139 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 139 = false := rfl
theorem advanceAt139_north : advance soko2_2.board 139 .north = some 117 := by decide +kernel
theorem advanceAt139_south : advance soko2_2.board 139 .south = some 161 := by decide +kernel
theorem advanceAt139_east : advance soko2_2.board 139 .east = some 140 := by decide +kernel
theorem advanceAt139_west : advance soko2_2.board 139 .west = some 138 := by decide +kernel
theorem advanceAt139_northEast : advance soko2_2.board 139 .northEast = some 118 := by decide +kernel
theorem advanceAt139_northWest : advance soko2_2.board 139 .northWest = some 116 := by decide +kernel
theorem advanceAt139_southEast : advance soko2_2.board 139 .southEast = some 162 := by decide +kernel
theorem advanceAt139_southWest : advance soko2_2.board 139 .southWest = some 160 := by decide +kernel
theorem floorAt140 : soko2_2.board.floor.contains 140 = false := by decide +kernel
theorem doorAt140 : soko2_2.board.doors.contains 140 = false := by decide +kernel
theorem trapAt140 : soko2_2.board.rollingTraps.contains 140 = false := by decide +kernel
theorem boxAt140 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 140 = false := rfl
theorem holeAt140 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 140 = false := rfl
theorem advanceAt140_north : advance soko2_2.board 140 .north = some 118 := by decide +kernel
theorem advanceAt140_south : advance soko2_2.board 140 .south = some 162 := by decide +kernel
theorem advanceAt140_east : advance soko2_2.board 140 .east = some 141 := by decide +kernel
theorem advanceAt140_west : advance soko2_2.board 140 .west = some 139 := by decide +kernel
theorem advanceAt140_northEast : advance soko2_2.board 140 .northEast = some 119 := by decide +kernel
theorem advanceAt140_northWest : advance soko2_2.board 140 .northWest = some 117 := by decide +kernel
theorem advanceAt140_southEast : advance soko2_2.board 140 .southEast = some 163 := by decide +kernel
theorem advanceAt140_southWest : advance soko2_2.board 140 .southWest = some 161 := by decide +kernel
theorem floorAt141 : soko2_2.board.floor.contains 141 = true := by decide +kernel
theorem doorAt141 : soko2_2.board.doors.contains 141 = false := by decide +kernel
theorem trapAt141 : soko2_2.board.rollingTraps.contains 141 = false := by decide +kernel
theorem boxAt141 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 141 = p 141 := rfl
theorem holeAt141 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 141 = false := rfl
theorem advanceAt141_north : advance soko2_2.board 141 .north = some 119 := by decide +kernel
theorem advanceAt141_south : advance soko2_2.board 141 .south = some 163 := by decide +kernel
theorem advanceAt141_east : advance soko2_2.board 141 .east = some 142 := by decide +kernel
theorem advanceAt141_west : advance soko2_2.board 141 .west = some 140 := by decide +kernel
theorem advanceAt141_northEast : advance soko2_2.board 141 .northEast = some 120 := by decide +kernel
theorem advanceAt141_northWest : advance soko2_2.board 141 .northWest = some 118 := by decide +kernel
theorem advanceAt141_southEast : advance soko2_2.board 141 .southEast = some 164 := by decide +kernel
theorem advanceAt141_southWest : advance soko2_2.board 141 .southWest = some 162 := by decide +kernel
theorem floorAt142 : soko2_2.board.floor.contains 142 = false := by decide +kernel
theorem doorAt142 : soko2_2.board.doors.contains 142 = false := by decide +kernel
theorem trapAt142 : soko2_2.board.rollingTraps.contains 142 = false := by decide +kernel
theorem boxAt142 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 142 = false := rfl
theorem holeAt142 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 142 = false := rfl
theorem advanceAt142_north : advance soko2_2.board 142 .north = some 120 := by decide +kernel
theorem advanceAt142_south : advance soko2_2.board 142 .south = some 164 := by decide +kernel
theorem advanceAt142_east : advance soko2_2.board 142 .east = some 143 := by decide +kernel
theorem advanceAt142_west : advance soko2_2.board 142 .west = some 141 := by decide +kernel
theorem advanceAt142_northEast : advance soko2_2.board 142 .northEast = some 121 := by decide +kernel
theorem advanceAt142_northWest : advance soko2_2.board 142 .northWest = some 119 := by decide +kernel
theorem advanceAt142_southEast : advance soko2_2.board 142 .southEast = some 165 := by decide +kernel
theorem advanceAt142_southWest : advance soko2_2.board 142 .southWest = some 163 := by decide +kernel
theorem floorAt143 : soko2_2.board.floor.contains 143 = false := by decide +kernel
theorem doorAt143 : soko2_2.board.doors.contains 143 = false := by decide +kernel
theorem trapAt143 : soko2_2.board.rollingTraps.contains 143 = false := by decide +kernel
theorem boxAt143 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 143 = false := rfl
theorem holeAt143 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 143 = false := rfl
theorem advanceAt143_north : advance soko2_2.board 143 .north = some 121 := by decide +kernel
theorem advanceAt143_south : advance soko2_2.board 143 .south = some 165 := by decide +kernel
theorem advanceAt143_east : advance soko2_2.board 143 .east = some 144 := by decide +kernel
theorem advanceAt143_west : advance soko2_2.board 143 .west = some 142 := by decide +kernel
theorem advanceAt143_northEast : advance soko2_2.board 143 .northEast = some 122 := by decide +kernel
theorem advanceAt143_northWest : advance soko2_2.board 143 .northWest = some 120 := by decide +kernel
theorem advanceAt143_southEast : advance soko2_2.board 143 .southEast = some 166 := by decide +kernel
theorem advanceAt143_southWest : advance soko2_2.board 143 .southWest = some 164 := by decide +kernel
theorem floorAt144 : soko2_2.board.floor.contains 144 = true := by decide +kernel
theorem doorAt144 : soko2_2.board.doors.contains 144 = false := by decide +kernel
theorem trapAt144 : soko2_2.board.rollingTraps.contains 144 = false := by decide +kernel
theorem boxAt144 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 144 = false := rfl
theorem holeAt144 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 144 = false := rfl
theorem advanceAt144_north : advance soko2_2.board 144 .north = some 122 := by decide +kernel
theorem advanceAt144_south : advance soko2_2.board 144 .south = some 166 := by decide +kernel
theorem advanceAt144_east : advance soko2_2.board 144 .east = some 145 := by decide +kernel
theorem advanceAt144_west : advance soko2_2.board 144 .west = some 143 := by decide +kernel
theorem advanceAt144_northEast : advance soko2_2.board 144 .northEast = some 123 := by decide +kernel
theorem advanceAt144_northWest : advance soko2_2.board 144 .northWest = some 121 := by decide +kernel
theorem advanceAt144_southEast : advance soko2_2.board 144 .southEast = some 167 := by decide +kernel
theorem advanceAt144_southWest : advance soko2_2.board 144 .southWest = some 165 := by decide +kernel
theorem floorAt145 : soko2_2.board.floor.contains 145 = true := by decide +kernel
theorem doorAt145 : soko2_2.board.doors.contains 145 = false := by decide +kernel
theorem trapAt145 : soko2_2.board.rollingTraps.contains 145 = false := by decide +kernel
theorem boxAt145 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 145 = false := rfl
theorem holeAt145 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 145 = false := rfl
theorem advanceAt145_north : advance soko2_2.board 145 .north = some 123 := by decide +kernel
theorem advanceAt145_south : advance soko2_2.board 145 .south = some 167 := by decide +kernel
theorem advanceAt145_east : advance soko2_2.board 145 .east = some 146 := by decide +kernel
theorem advanceAt145_west : advance soko2_2.board 145 .west = some 144 := by decide +kernel
theorem advanceAt145_northEast : advance soko2_2.board 145 .northEast = some 124 := by decide +kernel
theorem advanceAt145_northWest : advance soko2_2.board 145 .northWest = some 122 := by decide +kernel
theorem advanceAt145_southEast : advance soko2_2.board 145 .southEast = some 168 := by decide +kernel
theorem advanceAt145_southWest : advance soko2_2.board 145 .southWest = some 166 := by decide +kernel
theorem floorAt146 : soko2_2.board.floor.contains 146 = true := by decide +kernel
theorem doorAt146 : soko2_2.board.doors.contains 146 = false := by decide +kernel
theorem trapAt146 : soko2_2.board.rollingTraps.contains 146 = false := by decide +kernel
theorem boxAt146 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 146 = false := rfl
theorem holeAt146 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 146 = false := rfl
theorem advanceAt146_north : advance soko2_2.board 146 .north = some 124 := by decide +kernel
theorem advanceAt146_south : advance soko2_2.board 146 .south = some 168 := by decide +kernel
theorem advanceAt146_east : advance soko2_2.board 146 .east = some 147 := by decide +kernel
theorem advanceAt146_west : advance soko2_2.board 146 .west = some 145 := by decide +kernel
theorem advanceAt146_northEast : advance soko2_2.board 146 .northEast = some 125 := by decide +kernel
theorem advanceAt146_northWest : advance soko2_2.board 146 .northWest = some 123 := by decide +kernel
theorem advanceAt146_southEast : advance soko2_2.board 146 .southEast = some 169 := by decide +kernel
theorem advanceAt146_southWest : advance soko2_2.board 146 .southWest = some 167 := by decide +kernel
theorem floorAt147 : soko2_2.board.floor.contains 147 = true := by decide +kernel
theorem doorAt147 : soko2_2.board.doors.contains 147 = false := by decide +kernel
theorem trapAt147 : soko2_2.board.rollingTraps.contains 147 = false := by decide +kernel
theorem boxAt147 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 147 = false := rfl
theorem holeAt147 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 147 = false := rfl
theorem advanceAt147_north : advance soko2_2.board 147 .north = some 125 := by decide +kernel
theorem advanceAt147_south : advance soko2_2.board 147 .south = some 169 := by decide +kernel
theorem advanceAt147_east : advance soko2_2.board 147 .east = some 148 := by decide +kernel
theorem advanceAt147_west : advance soko2_2.board 147 .west = some 146 := by decide +kernel
theorem advanceAt147_northEast : advance soko2_2.board 147 .northEast = some 126 := by decide +kernel
theorem advanceAt147_northWest : advance soko2_2.board 147 .northWest = some 124 := by decide +kernel
theorem advanceAt147_southEast : advance soko2_2.board 147 .southEast = some 170 := by decide +kernel
theorem advanceAt147_southWest : advance soko2_2.board 147 .southWest = some 168 := by decide +kernel
theorem floorAt148 : soko2_2.board.floor.contains 148 = true := by decide +kernel
theorem doorAt148 : soko2_2.board.doors.contains 148 = false := by decide +kernel
theorem trapAt148 : soko2_2.board.rollingTraps.contains 148 = false := by decide +kernel
theorem boxAt148 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 148 = false := rfl
theorem holeAt148 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 148 = false := rfl
theorem advanceAt148_north : advance soko2_2.board 148 .north = some 126 := by decide +kernel
theorem advanceAt148_south : advance soko2_2.board 148 .south = some 170 := by decide +kernel
theorem advanceAt148_east : advance soko2_2.board 148 .east = some 149 := by decide +kernel
theorem advanceAt148_west : advance soko2_2.board 148 .west = some 147 := by decide +kernel
theorem advanceAt148_northEast : advance soko2_2.board 148 .northEast = some 127 := by decide +kernel
theorem advanceAt148_northWest : advance soko2_2.board 148 .northWest = some 125 := by decide +kernel
theorem advanceAt148_southEast : advance soko2_2.board 148 .southEast = some 171 := by decide +kernel
theorem advanceAt148_southWest : advance soko2_2.board 148 .southWest = some 169 := by decide +kernel
theorem floorAt149 : soko2_2.board.floor.contains 149 = true := by decide +kernel
theorem doorAt149 : soko2_2.board.doors.contains 149 = false := by decide +kernel
theorem trapAt149 : soko2_2.board.rollingTraps.contains 149 = false := by decide +kernel
theorem boxAt149 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 149 = false := rfl
theorem holeAt149 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 149 = false := rfl
theorem advanceAt149_north : advance soko2_2.board 149 .north = some 127 := by decide +kernel
theorem advanceAt149_south : advance soko2_2.board 149 .south = some 171 := by decide +kernel
theorem advanceAt149_east : advance soko2_2.board 149 .east = some 150 := by decide +kernel
theorem advanceAt149_west : advance soko2_2.board 149 .west = some 148 := by decide +kernel
theorem advanceAt149_northEast : advance soko2_2.board 149 .northEast = some 128 := by decide +kernel
theorem advanceAt149_northWest : advance soko2_2.board 149 .northWest = some 126 := by decide +kernel
theorem advanceAt149_southEast : advance soko2_2.board 149 .southEast = some 172 := by decide +kernel
theorem advanceAt149_southWest : advance soko2_2.board 149 .southWest = some 170 := by decide +kernel
theorem floorAt150 : soko2_2.board.floor.contains 150 = true := by decide +kernel
theorem doorAt150 : soko2_2.board.doors.contains 150 = false := by decide +kernel
theorem trapAt150 : soko2_2.board.rollingTraps.contains 150 = false := by decide +kernel
theorem boxAt150 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 150 = false := rfl
theorem holeAt150 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 150 = false := rfl
theorem advanceAt150_north : advance soko2_2.board 150 .north = some 128 := by decide +kernel
theorem advanceAt150_south : advance soko2_2.board 150 .south = some 172 := by decide +kernel
theorem advanceAt150_east : advance soko2_2.board 150 .east = some 151 := by decide +kernel
theorem advanceAt150_west : advance soko2_2.board 150 .west = some 149 := by decide +kernel
theorem advanceAt150_northEast : advance soko2_2.board 150 .northEast = some 129 := by decide +kernel
theorem advanceAt150_northWest : advance soko2_2.board 150 .northWest = some 127 := by decide +kernel
theorem advanceAt150_southEast : advance soko2_2.board 150 .southEast = some 173 := by decide +kernel
theorem advanceAt150_southWest : advance soko2_2.board 150 .southWest = some 171 := by decide +kernel
theorem floorAt151 : soko2_2.board.floor.contains 151 = false := by decide +kernel
theorem doorAt151 : soko2_2.board.doors.contains 151 = false := by decide +kernel
theorem trapAt151 : soko2_2.board.rollingTraps.contains 151 = false := by decide +kernel
theorem boxAt151 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 151 = false := rfl
theorem holeAt151 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 151 = false := rfl
theorem advanceAt151_north : advance soko2_2.board 151 .north = some 129 := by decide +kernel
theorem advanceAt151_south : advance soko2_2.board 151 .south = some 173 := by decide +kernel
theorem advanceAt151_east : advance soko2_2.board 151 .east = some 152 := by decide +kernel
theorem advanceAt151_west : advance soko2_2.board 151 .west = some 150 := by decide +kernel
theorem advanceAt151_northEast : advance soko2_2.board 151 .northEast = some 130 := by decide +kernel
theorem advanceAt151_northWest : advance soko2_2.board 151 .northWest = some 128 := by decide +kernel
theorem advanceAt151_southEast : advance soko2_2.board 151 .southEast = some 174 := by decide +kernel
theorem advanceAt151_southWest : advance soko2_2.board 151 .southWest = some 172 := by decide +kernel
theorem floorAt152 : soko2_2.board.floor.contains 152 = false := by decide +kernel
theorem doorAt152 : soko2_2.board.doors.contains 152 = false := by decide +kernel
theorem trapAt152 : soko2_2.board.rollingTraps.contains 152 = false := by decide +kernel
theorem boxAt152 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 152 = false := rfl
theorem holeAt152 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 152 = false := rfl
theorem advanceAt152_north : advance soko2_2.board 152 .north = some 130 := by decide +kernel
theorem advanceAt152_south : advance soko2_2.board 152 .south = some 174 := by decide +kernel
theorem advanceAt152_east : advance soko2_2.board 152 .east = some 153 := by decide +kernel
theorem advanceAt152_west : advance soko2_2.board 152 .west = some 151 := by decide +kernel
theorem advanceAt152_northEast : advance soko2_2.board 152 .northEast = some 131 := by decide +kernel
theorem advanceAt152_northWest : advance soko2_2.board 152 .northWest = some 129 := by decide +kernel
theorem advanceAt152_southEast : advance soko2_2.board 152 .southEast = some 175 := by decide +kernel
theorem advanceAt152_southWest : advance soko2_2.board 152 .southWest = some 173 := by decide +kernel
theorem floorAt153 : soko2_2.board.floor.contains 153 = false := by decide +kernel
theorem doorAt153 : soko2_2.board.doors.contains 153 = false := by decide +kernel
theorem trapAt153 : soko2_2.board.rollingTraps.contains 153 = false := by decide +kernel
theorem boxAt153 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 153 = false := rfl
theorem holeAt153 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 153 = false := rfl
theorem advanceAt153_north : advance soko2_2.board 153 .north = some 131 := by decide +kernel
theorem advanceAt153_south : advance soko2_2.board 153 .south = some 175 := by decide +kernel
theorem advanceAt153_east : advance soko2_2.board 153 .east = none := by decide +kernel
theorem advanceAt153_west : advance soko2_2.board 153 .west = some 152 := by decide +kernel
theorem advanceAt153_northEast : advance soko2_2.board 153 .northEast = none := by decide +kernel
theorem advanceAt153_northWest : advance soko2_2.board 153 .northWest = some 130 := by decide +kernel
theorem advanceAt153_southEast : advance soko2_2.board 153 .southEast = none := by decide +kernel
theorem advanceAt153_southWest : advance soko2_2.board 153 .southWest = some 174 := by decide +kernel
theorem floorAt154 : soko2_2.board.floor.contains 154 = false := by decide +kernel
theorem doorAt154 : soko2_2.board.doors.contains 154 = false := by decide +kernel
theorem trapAt154 : soko2_2.board.rollingTraps.contains 154 = false := by decide +kernel
theorem boxAt154 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 154 = false := rfl
theorem holeAt154 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 154 = false := rfl
theorem advanceAt154_north : advance soko2_2.board 154 .north = some 132 := by decide +kernel
theorem advanceAt154_south : advance soko2_2.board 154 .south = some 176 := by decide +kernel
theorem advanceAt154_east : advance soko2_2.board 154 .east = some 155 := by decide +kernel
theorem advanceAt154_west : advance soko2_2.board 154 .west = none := by decide +kernel
theorem advanceAt154_northEast : advance soko2_2.board 154 .northEast = some 133 := by decide +kernel
theorem advanceAt154_northWest : advance soko2_2.board 154 .northWest = none := by decide +kernel
theorem advanceAt154_southEast : advance soko2_2.board 154 .southEast = some 177 := by decide +kernel
theorem advanceAt154_southWest : advance soko2_2.board 154 .southWest = none := by decide +kernel
theorem floorAt155 : soko2_2.board.floor.contains 155 = true := by decide +kernel
theorem doorAt155 : soko2_2.board.doors.contains 155 = false := by decide +kernel
theorem trapAt155 : soko2_2.board.rollingTraps.contains 155 = false := by decide +kernel
theorem boxAt155 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 155 = p 155 := rfl
theorem holeAt155 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 155 = false := rfl
theorem advanceAt155_north : advance soko2_2.board 155 .north = some 133 := by decide +kernel
theorem advanceAt155_south : advance soko2_2.board 155 .south = some 177 := by decide +kernel
theorem advanceAt155_east : advance soko2_2.board 155 .east = some 156 := by decide +kernel
theorem advanceAt155_west : advance soko2_2.board 155 .west = some 154 := by decide +kernel
theorem advanceAt155_northEast : advance soko2_2.board 155 .northEast = some 134 := by decide +kernel
theorem advanceAt155_northWest : advance soko2_2.board 155 .northWest = some 132 := by decide +kernel
theorem advanceAt155_southEast : advance soko2_2.board 155 .southEast = some 178 := by decide +kernel
theorem advanceAt155_southWest : advance soko2_2.board 155 .southWest = some 176 := by decide +kernel
theorem floorAt156 : soko2_2.board.floor.contains 156 = true := by decide +kernel
theorem doorAt156 : soko2_2.board.doors.contains 156 = false := by decide +kernel
theorem trapAt156 : soko2_2.board.rollingTraps.contains 156 = false := by decide +kernel
theorem boxAt156 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 156 = p 156 := rfl
theorem holeAt156 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 156 = false := rfl
theorem advanceAt156_north : advance soko2_2.board 156 .north = some 134 := by decide +kernel
theorem advanceAt156_south : advance soko2_2.board 156 .south = some 178 := by decide +kernel
theorem advanceAt156_east : advance soko2_2.board 156 .east = some 157 := by decide +kernel
theorem advanceAt156_west : advance soko2_2.board 156 .west = some 155 := by decide +kernel
theorem advanceAt156_northEast : advance soko2_2.board 156 .northEast = some 135 := by decide +kernel
theorem advanceAt156_northWest : advance soko2_2.board 156 .northWest = some 133 := by decide +kernel
theorem advanceAt156_southEast : advance soko2_2.board 156 .southEast = some 179 := by decide +kernel
theorem advanceAt156_southWest : advance soko2_2.board 156 .southWest = some 177 := by decide +kernel
theorem floorAt157 : soko2_2.board.floor.contains 157 = true := by decide +kernel
theorem doorAt157 : soko2_2.board.doors.contains 157 = false := by decide +kernel
theorem trapAt157 : soko2_2.board.rollingTraps.contains 157 = false := by decide +kernel
theorem boxAt157 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 157 = p 157 := rfl
theorem holeAt157 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 157 = false := rfl
theorem advanceAt157_north : advance soko2_2.board 157 .north = some 135 := by decide +kernel
theorem advanceAt157_south : advance soko2_2.board 157 .south = some 179 := by decide +kernel
theorem advanceAt157_east : advance soko2_2.board 157 .east = some 158 := by decide +kernel
theorem advanceAt157_west : advance soko2_2.board 157 .west = some 156 := by decide +kernel
theorem advanceAt157_northEast : advance soko2_2.board 157 .northEast = some 136 := by decide +kernel
theorem advanceAt157_northWest : advance soko2_2.board 157 .northWest = some 134 := by decide +kernel
theorem advanceAt157_southEast : advance soko2_2.board 157 .southEast = some 180 := by decide +kernel
theorem advanceAt157_southWest : advance soko2_2.board 157 .southWest = some 178 := by decide +kernel
theorem floorAt158 : soko2_2.board.floor.contains 158 = true := by decide +kernel
theorem doorAt158 : soko2_2.board.doors.contains 158 = false := by decide +kernel
theorem trapAt158 : soko2_2.board.rollingTraps.contains 158 = false := by decide +kernel
theorem boxAt158 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 158 = p 158 := rfl
theorem holeAt158 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 158 = false := rfl
theorem advanceAt158_north : advance soko2_2.board 158 .north = some 136 := by decide +kernel
theorem advanceAt158_south : advance soko2_2.board 158 .south = some 180 := by decide +kernel
theorem advanceAt158_east : advance soko2_2.board 158 .east = some 159 := by decide +kernel
theorem advanceAt158_west : advance soko2_2.board 158 .west = some 157 := by decide +kernel
theorem advanceAt158_northEast : advance soko2_2.board 158 .northEast = some 137 := by decide +kernel
theorem advanceAt158_northWest : advance soko2_2.board 158 .northWest = some 135 := by decide +kernel
theorem advanceAt158_southEast : advance soko2_2.board 158 .southEast = some 181 := by decide +kernel
theorem advanceAt158_southWest : advance soko2_2.board 158 .southWest = some 179 := by decide +kernel
theorem floorAt159 : soko2_2.board.floor.contains 159 = true := by decide +kernel
theorem doorAt159 : soko2_2.board.doors.contains 159 = false := by decide +kernel
theorem trapAt159 : soko2_2.board.rollingTraps.contains 159 = false := by decide +kernel
theorem boxAt159 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 159 = p 159 := rfl
theorem holeAt159 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 159 = false := rfl
theorem advanceAt159_north : advance soko2_2.board 159 .north = some 137 := by decide +kernel
theorem advanceAt159_south : advance soko2_2.board 159 .south = some 181 := by decide +kernel
theorem advanceAt159_east : advance soko2_2.board 159 .east = some 160 := by decide +kernel
theorem advanceAt159_west : advance soko2_2.board 159 .west = some 158 := by decide +kernel
theorem advanceAt159_northEast : advance soko2_2.board 159 .northEast = some 138 := by decide +kernel
theorem advanceAt159_northWest : advance soko2_2.board 159 .northWest = some 136 := by decide +kernel
theorem advanceAt159_southEast : advance soko2_2.board 159 .southEast = some 182 := by decide +kernel
theorem advanceAt159_southWest : advance soko2_2.board 159 .southWest = some 180 := by decide +kernel
end NetHack.Soko22Hazard87
