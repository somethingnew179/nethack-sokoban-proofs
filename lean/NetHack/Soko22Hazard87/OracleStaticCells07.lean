import NetHack.Soko22Hazard87.OracleStaticCells06
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem floorAt280 : soko2_2.board.floor.contains 280 = false := by decide +kernel
theorem doorAt280 : soko2_2.board.doors.contains 280 = false := by decide +kernel
theorem trapAt280 : soko2_2.board.rollingTraps.contains 280 = false := by decide +kernel
theorem boxAt280 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 280 = false := rfl
theorem holeAt280 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 280 = false := rfl
theorem advanceAt280_north : advance soko2_2.board 280 .north = some 258 := by decide +kernel
theorem advanceAt280_south : advance soko2_2.board 280 .south = none := by decide +kernel
theorem advanceAt280_east : advance soko2_2.board 280 .east = some 281 := by decide +kernel
theorem advanceAt280_west : advance soko2_2.board 280 .west = some 279 := by decide +kernel
theorem advanceAt280_northEast : advance soko2_2.board 280 .northEast = some 259 := by decide +kernel
theorem advanceAt280_northWest : advance soko2_2.board 280 .northWest = some 257 := by decide +kernel
theorem advanceAt280_southEast : advance soko2_2.board 280 .southEast = none := by decide +kernel
theorem advanceAt280_southWest : advance soko2_2.board 280 .southWest = none := by decide +kernel
theorem floorAt281 : soko2_2.board.floor.contains 281 = false := by decide +kernel
theorem doorAt281 : soko2_2.board.doors.contains 281 = false := by decide +kernel
theorem trapAt281 : soko2_2.board.rollingTraps.contains 281 = false := by decide +kernel
theorem boxAt281 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 281 = false := rfl
theorem holeAt281 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 281 = false := rfl
theorem advanceAt281_north : advance soko2_2.board 281 .north = some 259 := by decide +kernel
theorem advanceAt281_south : advance soko2_2.board 281 .south = none := by decide +kernel
theorem advanceAt281_east : advance soko2_2.board 281 .east = some 282 := by decide +kernel
theorem advanceAt281_west : advance soko2_2.board 281 .west = some 280 := by decide +kernel
theorem advanceAt281_northEast : advance soko2_2.board 281 .northEast = some 260 := by decide +kernel
theorem advanceAt281_northWest : advance soko2_2.board 281 .northWest = some 258 := by decide +kernel
theorem advanceAt281_southEast : advance soko2_2.board 281 .southEast = none := by decide +kernel
theorem advanceAt281_southWest : advance soko2_2.board 281 .southWest = none := by decide +kernel
theorem floorAt282 : soko2_2.board.floor.contains 282 = false := by decide +kernel
theorem doorAt282 : soko2_2.board.doors.contains 282 = false := by decide +kernel
theorem trapAt282 : soko2_2.board.rollingTraps.contains 282 = false := by decide +kernel
theorem boxAt282 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 282 = false := rfl
theorem holeAt282 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 282 = false := rfl
theorem advanceAt282_north : advance soko2_2.board 282 .north = some 260 := by decide +kernel
theorem advanceAt282_south : advance soko2_2.board 282 .south = none := by decide +kernel
theorem advanceAt282_east : advance soko2_2.board 282 .east = some 283 := by decide +kernel
theorem advanceAt282_west : advance soko2_2.board 282 .west = some 281 := by decide +kernel
theorem advanceAt282_northEast : advance soko2_2.board 282 .northEast = some 261 := by decide +kernel
theorem advanceAt282_northWest : advance soko2_2.board 282 .northWest = some 259 := by decide +kernel
theorem advanceAt282_southEast : advance soko2_2.board 282 .southEast = none := by decide +kernel
theorem advanceAt282_southWest : advance soko2_2.board 282 .southWest = none := by decide +kernel
theorem floorAt283 : soko2_2.board.floor.contains 283 = false := by decide +kernel
theorem doorAt283 : soko2_2.board.doors.contains 283 = false := by decide +kernel
theorem trapAt283 : soko2_2.board.rollingTraps.contains 283 = false := by decide +kernel
theorem boxAt283 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 283 = false := rfl
theorem holeAt283 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 283 = false := rfl
theorem advanceAt283_north : advance soko2_2.board 283 .north = some 261 := by decide +kernel
theorem advanceAt283_south : advance soko2_2.board 283 .south = none := by decide +kernel
theorem advanceAt283_east : advance soko2_2.board 283 .east = some 284 := by decide +kernel
theorem advanceAt283_west : advance soko2_2.board 283 .west = some 282 := by decide +kernel
theorem advanceAt283_northEast : advance soko2_2.board 283 .northEast = some 262 := by decide +kernel
theorem advanceAt283_northWest : advance soko2_2.board 283 .northWest = some 260 := by decide +kernel
theorem advanceAt283_southEast : advance soko2_2.board 283 .southEast = none := by decide +kernel
theorem advanceAt283_southWest : advance soko2_2.board 283 .southWest = none := by decide +kernel
theorem floorAt284 : soko2_2.board.floor.contains 284 = false := by decide +kernel
theorem doorAt284 : soko2_2.board.doors.contains 284 = false := by decide +kernel
theorem trapAt284 : soko2_2.board.rollingTraps.contains 284 = false := by decide +kernel
theorem boxAt284 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 284 = false := rfl
theorem holeAt284 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 284 = false := rfl
theorem advanceAt284_north : advance soko2_2.board 284 .north = some 262 := by decide +kernel
theorem advanceAt284_south : advance soko2_2.board 284 .south = none := by decide +kernel
theorem advanceAt284_east : advance soko2_2.board 284 .east = some 285 := by decide +kernel
theorem advanceAt284_west : advance soko2_2.board 284 .west = some 283 := by decide +kernel
theorem advanceAt284_northEast : advance soko2_2.board 284 .northEast = some 263 := by decide +kernel
theorem advanceAt284_northWest : advance soko2_2.board 284 .northWest = some 261 := by decide +kernel
theorem advanceAt284_southEast : advance soko2_2.board 284 .southEast = none := by decide +kernel
theorem advanceAt284_southWest : advance soko2_2.board 284 .southWest = none := by decide +kernel
theorem floorAt285 : soko2_2.board.floor.contains 285 = false := by decide +kernel
theorem doorAt285 : soko2_2.board.doors.contains 285 = false := by decide +kernel
theorem trapAt285 : soko2_2.board.rollingTraps.contains 285 = false := by decide +kernel
theorem boxAt285 (p : Pattern) : HazardPattern.boxes ClosedComponents.soko2_2Support p 285 = false := rfl
theorem holeAt285 (p : Pattern) : HazardPattern.hazards 10000 soko2_2.initial.holes p 285 = false := rfl
theorem advanceAt285_north : advance soko2_2.board 285 .north = some 263 := by decide +kernel
theorem advanceAt285_south : advance soko2_2.board 285 .south = none := by decide +kernel
theorem advanceAt285_east : advance soko2_2.board 285 .east = none := by decide +kernel
theorem advanceAt285_west : advance soko2_2.board 285 .west = some 284 := by decide +kernel
theorem advanceAt285_northEast : advance soko2_2.board 285 .northEast = none := by decide +kernel
theorem advanceAt285_northWest : advance soko2_2.board 285 .northWest = some 262 := by decide +kernel
theorem advanceAt285_southEast : advance soko2_2.board 285 .southEast = none := by decide +kernel
theorem advanceAt285_southWest : advance soko2_2.board 285 .southWest = none := by decide +kernel
end NetHack.Soko22Hazard87
