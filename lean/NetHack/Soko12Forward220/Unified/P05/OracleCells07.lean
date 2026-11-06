import NetHack.Soko12Forward220.Unified.P05.OracleCells06
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P05
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem floorAt280 : soko1_2.board.floor.contains 280 = true := by decide +kernel
theorem doorAt280 : soko1_2.board.doors.contains 280 = false := by decide +kernel
theorem trapAt280 : soko1_2.board.rollingTraps.contains 280 = false := by decide +kernel
theorem boxAt280 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 280 = false := rfl
theorem holeAt280 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 280 = false := rfl
theorem advanceAt280_north : advance soko1_2.board 280 .north = some 254 := by decide +kernel
theorem advanceAt280_south : advance soko1_2.board 280 .south = some 306 := by decide +kernel
theorem advanceAt280_east : advance soko1_2.board 280 .east = some 281 := by decide +kernel
theorem advanceAt280_west : advance soko1_2.board 280 .west = some 279 := by decide +kernel
theorem advanceAt280_northEast : advance soko1_2.board 280 .northEast = some 255 := by decide +kernel
theorem advanceAt280_northWest : advance soko1_2.board 280 .northWest = some 253 := by decide +kernel
theorem advanceAt280_southEast : advance soko1_2.board 280 .southEast = some 307 := by decide +kernel
theorem advanceAt280_southWest : advance soko1_2.board 280 .southWest = some 305 := by decide +kernel
theorem floorAt281 : soko1_2.board.floor.contains 281 = true := by decide +kernel
theorem doorAt281 : soko1_2.board.doors.contains 281 = false := by decide +kernel
theorem trapAt281 : soko1_2.board.rollingTraps.contains 281 = false := by decide +kernel
theorem boxAt281 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 281 = false := rfl
theorem holeAt281 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 281 = false := rfl
theorem advanceAt281_north : advance soko1_2.board 281 .north = some 255 := by decide +kernel
theorem advanceAt281_south : advance soko1_2.board 281 .south = some 307 := by decide +kernel
theorem advanceAt281_east : advance soko1_2.board 281 .east = some 282 := by decide +kernel
theorem advanceAt281_west : advance soko1_2.board 281 .west = some 280 := by decide +kernel
theorem advanceAt281_northEast : advance soko1_2.board 281 .northEast = some 256 := by decide +kernel
theorem advanceAt281_northWest : advance soko1_2.board 281 .northWest = some 254 := by decide +kernel
theorem advanceAt281_southEast : advance soko1_2.board 281 .southEast = some 308 := by decide +kernel
theorem advanceAt281_southWest : advance soko1_2.board 281 .southWest = some 306 := by decide +kernel
theorem floorAt282 : soko1_2.board.floor.contains 282 = true := by decide +kernel
theorem doorAt282 : soko1_2.board.doors.contains 282 = false := by decide +kernel
theorem trapAt282 : soko1_2.board.rollingTraps.contains 282 = false := by decide +kernel
theorem boxAt282 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 282 = false := rfl
theorem holeAt282 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 282 = false := rfl
theorem advanceAt282_north : advance soko1_2.board 282 .north = some 256 := by decide +kernel
theorem advanceAt282_south : advance soko1_2.board 282 .south = some 308 := by decide +kernel
theorem advanceAt282_east : advance soko1_2.board 282 .east = some 283 := by decide +kernel
theorem advanceAt282_west : advance soko1_2.board 282 .west = some 281 := by decide +kernel
theorem advanceAt282_northEast : advance soko1_2.board 282 .northEast = some 257 := by decide +kernel
theorem advanceAt282_northWest : advance soko1_2.board 282 .northWest = some 255 := by decide +kernel
theorem advanceAt282_southEast : advance soko1_2.board 282 .southEast = some 309 := by decide +kernel
theorem advanceAt282_southWest : advance soko1_2.board 282 .southWest = some 307 := by decide +kernel
theorem floorAt283 : soko1_2.board.floor.contains 283 = false := by decide +kernel
theorem doorAt283 : soko1_2.board.doors.contains 283 = false := by decide +kernel
theorem trapAt283 : soko1_2.board.rollingTraps.contains 283 = false := by decide +kernel
theorem boxAt283 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 283 = false := rfl
theorem holeAt283 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 283 = false := rfl
theorem advanceAt283_north : advance soko1_2.board 283 .north = some 257 := by decide +kernel
theorem advanceAt283_south : advance soko1_2.board 283 .south = some 309 := by decide +kernel
theorem advanceAt283_east : advance soko1_2.board 283 .east = some 284 := by decide +kernel
theorem advanceAt283_west : advance soko1_2.board 283 .west = some 282 := by decide +kernel
theorem advanceAt283_northEast : advance soko1_2.board 283 .northEast = some 258 := by decide +kernel
theorem advanceAt283_northWest : advance soko1_2.board 283 .northWest = some 256 := by decide +kernel
theorem advanceAt283_southEast : advance soko1_2.board 283 .southEast = some 310 := by decide +kernel
theorem advanceAt283_southWest : advance soko1_2.board 283 .southWest = some 308 := by decide +kernel
theorem floorAt284 : soko1_2.board.floor.contains 284 = true := by decide +kernel
theorem doorAt284 : soko1_2.board.doors.contains 284 = false := by decide +kernel
theorem trapAt284 : soko1_2.board.rollingTraps.contains 284 = false := by decide +kernel
theorem boxAt284 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 284 = false := rfl
theorem holeAt284 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 284 = false := rfl
theorem advanceAt284_north : advance soko1_2.board 284 .north = some 258 := by decide +kernel
theorem advanceAt284_south : advance soko1_2.board 284 .south = some 310 := by decide +kernel
theorem advanceAt284_east : advance soko1_2.board 284 .east = some 285 := by decide +kernel
theorem advanceAt284_west : advance soko1_2.board 284 .west = some 283 := by decide +kernel
theorem advanceAt284_northEast : advance soko1_2.board 284 .northEast = some 259 := by decide +kernel
theorem advanceAt284_northWest : advance soko1_2.board 284 .northWest = some 257 := by decide +kernel
theorem advanceAt284_southEast : advance soko1_2.board 284 .southEast = some 311 := by decide +kernel
theorem advanceAt284_southWest : advance soko1_2.board 284 .southWest = some 309 := by decide +kernel
theorem floorAt285 : soko1_2.board.floor.contains 285 = false := by decide +kernel
theorem doorAt285 : soko1_2.board.doors.contains 285 = false := by decide +kernel
theorem trapAt285 : soko1_2.board.rollingTraps.contains 285 = false := by decide +kernel
theorem boxAt285 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 285 = false := rfl
theorem holeAt285 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 285 = false := rfl
theorem advanceAt285_north : advance soko1_2.board 285 .north = some 259 := by decide +kernel
theorem advanceAt285_south : advance soko1_2.board 285 .south = some 311 := by decide +kernel
theorem advanceAt285_east : advance soko1_2.board 285 .east = none := by decide +kernel
theorem advanceAt285_west : advance soko1_2.board 285 .west = some 284 := by decide +kernel
theorem advanceAt285_northEast : advance soko1_2.board 285 .northEast = none := by decide +kernel
theorem advanceAt285_northWest : advance soko1_2.board 285 .northWest = some 258 := by decide +kernel
theorem advanceAt285_southEast : advance soko1_2.board 285 .southEast = none := by decide +kernel
theorem advanceAt285_southWest : advance soko1_2.board 285 .southWest = some 310 := by decide +kernel
theorem floorAt286 : soko1_2.board.floor.contains 286 = false := by decide +kernel
theorem doorAt286 : soko1_2.board.doors.contains 286 = false := by decide +kernel
theorem trapAt286 : soko1_2.board.rollingTraps.contains 286 = false := by decide +kernel
theorem boxAt286 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 286 = false := rfl
theorem holeAt286 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 286 = false := rfl
theorem advanceAt286_north : advance soko1_2.board 286 .north = some 260 := by decide +kernel
theorem advanceAt286_south : advance soko1_2.board 286 .south = some 312 := by decide +kernel
theorem advanceAt286_east : advance soko1_2.board 286 .east = some 287 := by decide +kernel
theorem advanceAt286_west : advance soko1_2.board 286 .west = none := by decide +kernel
theorem advanceAt286_northEast : advance soko1_2.board 286 .northEast = some 261 := by decide +kernel
theorem advanceAt286_northWest : advance soko1_2.board 286 .northWest = none := by decide +kernel
theorem advanceAt286_southEast : advance soko1_2.board 286 .southEast = some 313 := by decide +kernel
theorem advanceAt286_southWest : advance soko1_2.board 286 .southWest = none := by decide +kernel
theorem floorAt287 : soko1_2.board.floor.contains 287 = false := by decide +kernel
theorem doorAt287 : soko1_2.board.doors.contains 287 = false := by decide +kernel
theorem trapAt287 : soko1_2.board.rollingTraps.contains 287 = false := by decide +kernel
theorem boxAt287 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 287 = false := rfl
theorem holeAt287 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 287 = false := rfl
theorem advanceAt287_north : advance soko1_2.board 287 .north = some 261 := by decide +kernel
theorem advanceAt287_south : advance soko1_2.board 287 .south = some 313 := by decide +kernel
theorem advanceAt287_east : advance soko1_2.board 287 .east = some 288 := by decide +kernel
theorem advanceAt287_west : advance soko1_2.board 287 .west = some 286 := by decide +kernel
theorem advanceAt287_northEast : advance soko1_2.board 287 .northEast = some 262 := by decide +kernel
theorem advanceAt287_northWest : advance soko1_2.board 287 .northWest = some 260 := by decide +kernel
theorem advanceAt287_southEast : advance soko1_2.board 287 .southEast = some 314 := by decide +kernel
theorem advanceAt287_southWest : advance soko1_2.board 287 .southWest = some 312 := by decide +kernel
theorem floorAt288 : soko1_2.board.floor.contains 288 = true := by decide +kernel
theorem doorAt288 : soko1_2.board.doors.contains 288 = false := by decide +kernel
theorem trapAt288 : soko1_2.board.rollingTraps.contains 288 = false := by decide +kernel
theorem boxAt288 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 288 = p 288 := rfl
theorem holeAt288 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 288 = false := rfl
theorem advanceAt288_north : advance soko1_2.board 288 .north = some 262 := by decide +kernel
theorem advanceAt288_south : advance soko1_2.board 288 .south = some 314 := by decide +kernel
theorem advanceAt288_east : advance soko1_2.board 288 .east = some 289 := by decide +kernel
theorem advanceAt288_west : advance soko1_2.board 288 .west = some 287 := by decide +kernel
theorem advanceAt288_northEast : advance soko1_2.board 288 .northEast = some 263 := by decide +kernel
theorem advanceAt288_northWest : advance soko1_2.board 288 .northWest = some 261 := by decide +kernel
theorem advanceAt288_southEast : advance soko1_2.board 288 .southEast = some 315 := by decide +kernel
theorem advanceAt288_southWest : advance soko1_2.board 288 .southWest = some 313 := by decide +kernel
theorem floorAt289 : soko1_2.board.floor.contains 289 = true := by decide +kernel
theorem doorAt289 : soko1_2.board.doors.contains 289 = false := by decide +kernel
theorem trapAt289 : soko1_2.board.rollingTraps.contains 289 = false := by decide +kernel
theorem boxAt289 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 289 = p 289 := rfl
theorem holeAt289 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 289 = false := rfl
theorem advanceAt289_north : advance soko1_2.board 289 .north = some 263 := by decide +kernel
theorem advanceAt289_south : advance soko1_2.board 289 .south = some 315 := by decide +kernel
theorem advanceAt289_east : advance soko1_2.board 289 .east = some 290 := by decide +kernel
theorem advanceAt289_west : advance soko1_2.board 289 .west = some 288 := by decide +kernel
theorem advanceAt289_northEast : advance soko1_2.board 289 .northEast = some 264 := by decide +kernel
theorem advanceAt289_northWest : advance soko1_2.board 289 .northWest = some 262 := by decide +kernel
theorem advanceAt289_southEast : advance soko1_2.board 289 .southEast = some 316 := by decide +kernel
theorem advanceAt289_southWest : advance soko1_2.board 289 .southWest = some 314 := by decide +kernel
theorem floorAt290 : soko1_2.board.floor.contains 290 = true := by decide +kernel
theorem doorAt290 : soko1_2.board.doors.contains 290 = false := by decide +kernel
theorem trapAt290 : soko1_2.board.rollingTraps.contains 290 = false := by decide +kernel
theorem boxAt290 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 290 = p 290 := rfl
theorem holeAt290 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 290 = false := rfl
theorem advanceAt290_north : advance soko1_2.board 290 .north = some 264 := by decide +kernel
theorem advanceAt290_south : advance soko1_2.board 290 .south = some 316 := by decide +kernel
theorem advanceAt290_east : advance soko1_2.board 290 .east = some 291 := by decide +kernel
theorem advanceAt290_west : advance soko1_2.board 290 .west = some 289 := by decide +kernel
theorem advanceAt290_northEast : advance soko1_2.board 290 .northEast = some 265 := by decide +kernel
theorem advanceAt290_northWest : advance soko1_2.board 290 .northWest = some 263 := by decide +kernel
theorem advanceAt290_southEast : advance soko1_2.board 290 .southEast = some 317 := by decide +kernel
theorem advanceAt290_southWest : advance soko1_2.board 290 .southWest = some 315 := by decide +kernel
theorem floorAt291 : soko1_2.board.floor.contains 291 = true := by decide +kernel
theorem doorAt291 : soko1_2.board.doors.contains 291 = false := by decide +kernel
theorem trapAt291 : soko1_2.board.rollingTraps.contains 291 = false := by decide +kernel
theorem boxAt291 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 291 = p 291 := rfl
theorem holeAt291 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 291 = false := rfl
theorem advanceAt291_north : advance soko1_2.board 291 .north = some 265 := by decide +kernel
theorem advanceAt291_south : advance soko1_2.board 291 .south = some 317 := by decide +kernel
theorem advanceAt291_east : advance soko1_2.board 291 .east = some 292 := by decide +kernel
theorem advanceAt291_west : advance soko1_2.board 291 .west = some 290 := by decide +kernel
theorem advanceAt291_northEast : advance soko1_2.board 291 .northEast = some 266 := by decide +kernel
theorem advanceAt291_northWest : advance soko1_2.board 291 .northWest = some 264 := by decide +kernel
theorem advanceAt291_southEast : advance soko1_2.board 291 .southEast = some 318 := by decide +kernel
theorem advanceAt291_southWest : advance soko1_2.board 291 .southWest = some 316 := by decide +kernel
theorem floorAt292 : soko1_2.board.floor.contains 292 = true := by decide +kernel
theorem doorAt292 : soko1_2.board.doors.contains 292 = false := by decide +kernel
theorem trapAt292 : soko1_2.board.rollingTraps.contains 292 = false := by decide +kernel
theorem boxAt292 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 292 = p 292 := rfl
theorem holeAt292 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 292 = false := rfl
theorem advanceAt292_north : advance soko1_2.board 292 .north = some 266 := by decide +kernel
theorem advanceAt292_south : advance soko1_2.board 292 .south = some 318 := by decide +kernel
theorem advanceAt292_east : advance soko1_2.board 292 .east = some 293 := by decide +kernel
theorem advanceAt292_west : advance soko1_2.board 292 .west = some 291 := by decide +kernel
theorem advanceAt292_northEast : advance soko1_2.board 292 .northEast = some 267 := by decide +kernel
theorem advanceAt292_northWest : advance soko1_2.board 292 .northWest = some 265 := by decide +kernel
theorem advanceAt292_southEast : advance soko1_2.board 292 .southEast = some 319 := by decide +kernel
theorem advanceAt292_southWest : advance soko1_2.board 292 .southWest = some 317 := by decide +kernel
theorem floorAt293 : soko1_2.board.floor.contains 293 = true := by decide +kernel
theorem doorAt293 : soko1_2.board.doors.contains 293 = false := by decide +kernel
theorem trapAt293 : soko1_2.board.rollingTraps.contains 293 = false := by decide +kernel
theorem boxAt293 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 293 = p 293 := rfl
theorem holeAt293 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 293 = false := rfl
theorem advanceAt293_north : advance soko1_2.board 293 .north = some 267 := by decide +kernel
theorem advanceAt293_south : advance soko1_2.board 293 .south = some 319 := by decide +kernel
theorem advanceAt293_east : advance soko1_2.board 293 .east = some 294 := by decide +kernel
theorem advanceAt293_west : advance soko1_2.board 293 .west = some 292 := by decide +kernel
theorem advanceAt293_northEast : advance soko1_2.board 293 .northEast = some 268 := by decide +kernel
theorem advanceAt293_northWest : advance soko1_2.board 293 .northWest = some 266 := by decide +kernel
theorem advanceAt293_southEast : advance soko1_2.board 293 .southEast = some 320 := by decide +kernel
theorem advanceAt293_southWest : advance soko1_2.board 293 .southWest = some 318 := by decide +kernel
theorem floorAt294 : soko1_2.board.floor.contains 294 = true := by decide +kernel
theorem doorAt294 : soko1_2.board.doors.contains 294 = false := by decide +kernel
theorem trapAt294 : soko1_2.board.rollingTraps.contains 294 = false := by decide +kernel
theorem boxAt294 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 294 = p 294 := rfl
theorem holeAt294 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 294 = false := rfl
theorem advanceAt294_north : advance soko1_2.board 294 .north = some 268 := by decide +kernel
theorem advanceAt294_south : advance soko1_2.board 294 .south = some 320 := by decide +kernel
theorem advanceAt294_east : advance soko1_2.board 294 .east = some 295 := by decide +kernel
theorem advanceAt294_west : advance soko1_2.board 294 .west = some 293 := by decide +kernel
theorem advanceAt294_northEast : advance soko1_2.board 294 .northEast = some 269 := by decide +kernel
theorem advanceAt294_northWest : advance soko1_2.board 294 .northWest = some 267 := by decide +kernel
theorem advanceAt294_southEast : advance soko1_2.board 294 .southEast = some 321 := by decide +kernel
theorem advanceAt294_southWest : advance soko1_2.board 294 .southWest = some 319 := by decide +kernel
theorem floorAt295 : soko1_2.board.floor.contains 295 = false := by decide +kernel
theorem doorAt295 : soko1_2.board.doors.contains 295 = false := by decide +kernel
theorem trapAt295 : soko1_2.board.rollingTraps.contains 295 = false := by decide +kernel
theorem boxAt295 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 295 = false := rfl
theorem holeAt295 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 295 = false := rfl
theorem advanceAt295_north : advance soko1_2.board 295 .north = some 269 := by decide +kernel
theorem advanceAt295_south : advance soko1_2.board 295 .south = some 321 := by decide +kernel
theorem advanceAt295_east : advance soko1_2.board 295 .east = some 296 := by decide +kernel
theorem advanceAt295_west : advance soko1_2.board 295 .west = some 294 := by decide +kernel
theorem advanceAt295_northEast : advance soko1_2.board 295 .northEast = some 270 := by decide +kernel
theorem advanceAt295_northWest : advance soko1_2.board 295 .northWest = some 268 := by decide +kernel
theorem advanceAt295_southEast : advance soko1_2.board 295 .southEast = some 322 := by decide +kernel
theorem advanceAt295_southWest : advance soko1_2.board 295 .southWest = some 320 := by decide +kernel
theorem floorAt296 : soko1_2.board.floor.contains 296 = true := by decide +kernel
theorem doorAt296 : soko1_2.board.doors.contains 296 = false := by decide +kernel
theorem trapAt296 : soko1_2.board.rollingTraps.contains 296 = false := by decide +kernel
theorem boxAt296 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 296 = p 296 := rfl
theorem holeAt296 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 296 = false := rfl
theorem advanceAt296_north : advance soko1_2.board 296 .north = some 270 := by decide +kernel
theorem advanceAt296_south : advance soko1_2.board 296 .south = some 322 := by decide +kernel
theorem advanceAt296_east : advance soko1_2.board 296 .east = some 297 := by decide +kernel
theorem advanceAt296_west : advance soko1_2.board 296 .west = some 295 := by decide +kernel
theorem advanceAt296_northEast : advance soko1_2.board 296 .northEast = some 271 := by decide +kernel
theorem advanceAt296_northWest : advance soko1_2.board 296 .northWest = some 269 := by decide +kernel
theorem advanceAt296_southEast : advance soko1_2.board 296 .southEast = some 323 := by decide +kernel
theorem advanceAt296_southWest : advance soko1_2.board 296 .southWest = some 321 := by decide +kernel
theorem floorAt297 : soko1_2.board.floor.contains 297 = true := by decide +kernel
theorem doorAt297 : soko1_2.board.doors.contains 297 = false := by decide +kernel
theorem trapAt297 : soko1_2.board.rollingTraps.contains 297 = false := by decide +kernel
theorem boxAt297 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 297 = p 297 := rfl
theorem holeAt297 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 297 = false := rfl
theorem advanceAt297_north : advance soko1_2.board 297 .north = some 271 := by decide +kernel
theorem advanceAt297_south : advance soko1_2.board 297 .south = some 323 := by decide +kernel
theorem advanceAt297_east : advance soko1_2.board 297 .east = some 298 := by decide +kernel
theorem advanceAt297_west : advance soko1_2.board 297 .west = some 296 := by decide +kernel
theorem advanceAt297_northEast : advance soko1_2.board 297 .northEast = some 272 := by decide +kernel
theorem advanceAt297_northWest : advance soko1_2.board 297 .northWest = some 270 := by decide +kernel
theorem advanceAt297_southEast : advance soko1_2.board 297 .southEast = some 324 := by decide +kernel
theorem advanceAt297_southWest : advance soko1_2.board 297 .southWest = some 322 := by decide +kernel
theorem floorAt298 : soko1_2.board.floor.contains 298 = false := by decide +kernel
theorem doorAt298 : soko1_2.board.doors.contains 298 = false := by decide +kernel
theorem trapAt298 : soko1_2.board.rollingTraps.contains 298 = false := by decide +kernel
theorem boxAt298 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 298 = false := rfl
theorem holeAt298 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 298 = false := rfl
theorem advanceAt298_north : advance soko1_2.board 298 .north = some 272 := by decide +kernel
theorem advanceAt298_south : advance soko1_2.board 298 .south = some 324 := by decide +kernel
theorem advanceAt298_east : advance soko1_2.board 298 .east = some 299 := by decide +kernel
theorem advanceAt298_west : advance soko1_2.board 298 .west = some 297 := by decide +kernel
theorem advanceAt298_northEast : advance soko1_2.board 298 .northEast = some 273 := by decide +kernel
theorem advanceAt298_northWest : advance soko1_2.board 298 .northWest = some 271 := by decide +kernel
theorem advanceAt298_southEast : advance soko1_2.board 298 .southEast = some 325 := by decide +kernel
theorem advanceAt298_southWest : advance soko1_2.board 298 .southWest = some 323 := by decide +kernel
theorem floorAt299 : soko1_2.board.floor.contains 299 = false := by decide +kernel
theorem doorAt299 : soko1_2.board.doors.contains 299 = false := by decide +kernel
theorem trapAt299 : soko1_2.board.rollingTraps.contains 299 = false := by decide +kernel
theorem boxAt299 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 299 = false := rfl
theorem holeAt299 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 299 = false := rfl
theorem advanceAt299_north : advance soko1_2.board 299 .north = some 273 := by decide +kernel
theorem advanceAt299_south : advance soko1_2.board 299 .south = some 325 := by decide +kernel
theorem advanceAt299_east : advance soko1_2.board 299 .east = some 300 := by decide +kernel
theorem advanceAt299_west : advance soko1_2.board 299 .west = some 298 := by decide +kernel
theorem advanceAt299_northEast : advance soko1_2.board 299 .northEast = some 274 := by decide +kernel
theorem advanceAt299_northWest : advance soko1_2.board 299 .northWest = some 272 := by decide +kernel
theorem advanceAt299_southEast : advance soko1_2.board 299 .southEast = some 326 := by decide +kernel
theorem advanceAt299_southWest : advance soko1_2.board 299 .southWest = some 324 := by decide +kernel
theorem floorAt300 : soko1_2.board.floor.contains 300 = false := by decide +kernel
theorem doorAt300 : soko1_2.board.doors.contains 300 = false := by decide +kernel
theorem trapAt300 : soko1_2.board.rollingTraps.contains 300 = false := by decide +kernel
theorem boxAt300 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 300 = false := rfl
theorem holeAt300 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 300 = false := rfl
theorem advanceAt300_north : advance soko1_2.board 300 .north = some 274 := by decide +kernel
theorem advanceAt300_south : advance soko1_2.board 300 .south = some 326 := by decide +kernel
theorem advanceAt300_east : advance soko1_2.board 300 .east = some 301 := by decide +kernel
theorem advanceAt300_west : advance soko1_2.board 300 .west = some 299 := by decide +kernel
theorem advanceAt300_northEast : advance soko1_2.board 300 .northEast = some 275 := by decide +kernel
theorem advanceAt300_northWest : advance soko1_2.board 300 .northWest = some 273 := by decide +kernel
theorem advanceAt300_southEast : advance soko1_2.board 300 .southEast = some 327 := by decide +kernel
theorem advanceAt300_southWest : advance soko1_2.board 300 .southWest = some 325 := by decide +kernel
theorem floorAt301 : soko1_2.board.floor.contains 301 = false := by decide +kernel
theorem doorAt301 : soko1_2.board.doors.contains 301 = false := by decide +kernel
theorem trapAt301 : soko1_2.board.rollingTraps.contains 301 = false := by decide +kernel
theorem boxAt301 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 301 = false := rfl
theorem holeAt301 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 301 = false := rfl
theorem advanceAt301_north : advance soko1_2.board 301 .north = some 275 := by decide +kernel
theorem advanceAt301_south : advance soko1_2.board 301 .south = some 327 := by decide +kernel
theorem advanceAt301_east : advance soko1_2.board 301 .east = some 302 := by decide +kernel
theorem advanceAt301_west : advance soko1_2.board 301 .west = some 300 := by decide +kernel
theorem advanceAt301_northEast : advance soko1_2.board 301 .northEast = some 276 := by decide +kernel
theorem advanceAt301_northWest : advance soko1_2.board 301 .northWest = some 274 := by decide +kernel
theorem advanceAt301_southEast : advance soko1_2.board 301 .southEast = some 328 := by decide +kernel
theorem advanceAt301_southWest : advance soko1_2.board 301 .southWest = some 326 := by decide +kernel
theorem floorAt302 : soko1_2.board.floor.contains 302 = false := by decide +kernel
theorem doorAt302 : soko1_2.board.doors.contains 302 = false := by decide +kernel
theorem trapAt302 : soko1_2.board.rollingTraps.contains 302 = false := by decide +kernel
theorem boxAt302 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 302 = false := rfl
theorem holeAt302 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 302 = false := rfl
theorem advanceAt302_north : advance soko1_2.board 302 .north = some 276 := by decide +kernel
theorem advanceAt302_south : advance soko1_2.board 302 .south = some 328 := by decide +kernel
theorem advanceAt302_east : advance soko1_2.board 302 .east = some 303 := by decide +kernel
theorem advanceAt302_west : advance soko1_2.board 302 .west = some 301 := by decide +kernel
theorem advanceAt302_northEast : advance soko1_2.board 302 .northEast = some 277 := by decide +kernel
theorem advanceAt302_northWest : advance soko1_2.board 302 .northWest = some 275 := by decide +kernel
theorem advanceAt302_southEast : advance soko1_2.board 302 .southEast = some 329 := by decide +kernel
theorem advanceAt302_southWest : advance soko1_2.board 302 .southWest = some 327 := by decide +kernel
theorem floorAt303 : soko1_2.board.floor.contains 303 = false := by decide +kernel
theorem doorAt303 : soko1_2.board.doors.contains 303 = false := by decide +kernel
theorem trapAt303 : soko1_2.board.rollingTraps.contains 303 = false := by decide +kernel
theorem boxAt303 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 303 = false := rfl
theorem holeAt303 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 303 = false := rfl
theorem advanceAt303_north : advance soko1_2.board 303 .north = some 277 := by decide +kernel
theorem advanceAt303_south : advance soko1_2.board 303 .south = some 329 := by decide +kernel
theorem advanceAt303_east : advance soko1_2.board 303 .east = some 304 := by decide +kernel
theorem advanceAt303_west : advance soko1_2.board 303 .west = some 302 := by decide +kernel
theorem advanceAt303_northEast : advance soko1_2.board 303 .northEast = some 278 := by decide +kernel
theorem advanceAt303_northWest : advance soko1_2.board 303 .northWest = some 276 := by decide +kernel
theorem advanceAt303_southEast : advance soko1_2.board 303 .southEast = some 330 := by decide +kernel
theorem advanceAt303_southWest : advance soko1_2.board 303 .southWest = some 328 := by decide +kernel
theorem floorAt304 : soko1_2.board.floor.contains 304 = true := by decide +kernel
theorem doorAt304 : soko1_2.board.doors.contains 304 = false := by decide +kernel
theorem trapAt304 : soko1_2.board.rollingTraps.contains 304 = false := by decide +kernel
theorem boxAt304 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 304 = false := rfl
theorem holeAt304 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 304 = false := rfl
theorem advanceAt304_north : advance soko1_2.board 304 .north = some 278 := by decide +kernel
theorem advanceAt304_south : advance soko1_2.board 304 .south = some 330 := by decide +kernel
theorem advanceAt304_east : advance soko1_2.board 304 .east = some 305 := by decide +kernel
theorem advanceAt304_west : advance soko1_2.board 304 .west = some 303 := by decide +kernel
theorem advanceAt304_northEast : advance soko1_2.board 304 .northEast = some 279 := by decide +kernel
theorem advanceAt304_northWest : advance soko1_2.board 304 .northWest = some 277 := by decide +kernel
theorem advanceAt304_southEast : advance soko1_2.board 304 .southEast = some 331 := by decide +kernel
theorem advanceAt304_southWest : advance soko1_2.board 304 .southWest = some 329 := by decide +kernel
theorem floorAt305 : soko1_2.board.floor.contains 305 = true := by decide +kernel
theorem doorAt305 : soko1_2.board.doors.contains 305 = false := by decide +kernel
theorem trapAt305 : soko1_2.board.rollingTraps.contains 305 = false := by decide +kernel
theorem boxAt305 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 305 = false := rfl
theorem holeAt305 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 305 = false := rfl
theorem advanceAt305_north : advance soko1_2.board 305 .north = some 279 := by decide +kernel
theorem advanceAt305_south : advance soko1_2.board 305 .south = some 331 := by decide +kernel
theorem advanceAt305_east : advance soko1_2.board 305 .east = some 306 := by decide +kernel
theorem advanceAt305_west : advance soko1_2.board 305 .west = some 304 := by decide +kernel
theorem advanceAt305_northEast : advance soko1_2.board 305 .northEast = some 280 := by decide +kernel
theorem advanceAt305_northWest : advance soko1_2.board 305 .northWest = some 278 := by decide +kernel
theorem advanceAt305_southEast : advance soko1_2.board 305 .southEast = some 332 := by decide +kernel
theorem advanceAt305_southWest : advance soko1_2.board 305 .southWest = some 330 := by decide +kernel
theorem floorAt306 : soko1_2.board.floor.contains 306 = true := by decide +kernel
theorem doorAt306 : soko1_2.board.doors.contains 306 = false := by decide +kernel
theorem trapAt306 : soko1_2.board.rollingTraps.contains 306 = false := by decide +kernel
theorem boxAt306 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 306 = false := rfl
theorem holeAt306 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 306 = false := rfl
theorem advanceAt306_north : advance soko1_2.board 306 .north = some 280 := by decide +kernel
theorem advanceAt306_south : advance soko1_2.board 306 .south = some 332 := by decide +kernel
theorem advanceAt306_east : advance soko1_2.board 306 .east = some 307 := by decide +kernel
theorem advanceAt306_west : advance soko1_2.board 306 .west = some 305 := by decide +kernel
theorem advanceAt306_northEast : advance soko1_2.board 306 .northEast = some 281 := by decide +kernel
theorem advanceAt306_northWest : advance soko1_2.board 306 .northWest = some 279 := by decide +kernel
theorem advanceAt306_southEast : advance soko1_2.board 306 .southEast = some 333 := by decide +kernel
theorem advanceAt306_southWest : advance soko1_2.board 306 .southWest = some 331 := by decide +kernel
theorem floorAt307 : soko1_2.board.floor.contains 307 = true := by decide +kernel
theorem doorAt307 : soko1_2.board.doors.contains 307 = false := by decide +kernel
theorem trapAt307 : soko1_2.board.rollingTraps.contains 307 = false := by decide +kernel
theorem boxAt307 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 307 = false := rfl
theorem holeAt307 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 307 = false := rfl
theorem advanceAt307_north : advance soko1_2.board 307 .north = some 281 := by decide +kernel
theorem advanceAt307_south : advance soko1_2.board 307 .south = some 333 := by decide +kernel
theorem advanceAt307_east : advance soko1_2.board 307 .east = some 308 := by decide +kernel
theorem advanceAt307_west : advance soko1_2.board 307 .west = some 306 := by decide +kernel
theorem advanceAt307_northEast : advance soko1_2.board 307 .northEast = some 282 := by decide +kernel
theorem advanceAt307_northWest : advance soko1_2.board 307 .northWest = some 280 := by decide +kernel
theorem advanceAt307_southEast : advance soko1_2.board 307 .southEast = some 334 := by decide +kernel
theorem advanceAt307_southWest : advance soko1_2.board 307 .southWest = some 332 := by decide +kernel
theorem floorAt308 : soko1_2.board.floor.contains 308 = true := by decide +kernel
theorem doorAt308 : soko1_2.board.doors.contains 308 = false := by decide +kernel
theorem trapAt308 : soko1_2.board.rollingTraps.contains 308 = false := by decide +kernel
theorem boxAt308 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 308 = false := rfl
theorem holeAt308 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 308 = false := rfl
theorem advanceAt308_north : advance soko1_2.board 308 .north = some 282 := by decide +kernel
theorem advanceAt308_south : advance soko1_2.board 308 .south = some 334 := by decide +kernel
theorem advanceAt308_east : advance soko1_2.board 308 .east = some 309 := by decide +kernel
theorem advanceAt308_west : advance soko1_2.board 308 .west = some 307 := by decide +kernel
theorem advanceAt308_northEast : advance soko1_2.board 308 .northEast = some 283 := by decide +kernel
theorem advanceAt308_northWest : advance soko1_2.board 308 .northWest = some 281 := by decide +kernel
theorem advanceAt308_southEast : advance soko1_2.board 308 .southEast = some 335 := by decide +kernel
theorem advanceAt308_southWest : advance soko1_2.board 308 .southWest = some 333 := by decide +kernel
theorem floorAt309 : soko1_2.board.floor.contains 309 = false := by decide +kernel
theorem doorAt309 : soko1_2.board.doors.contains 309 = false := by decide +kernel
theorem trapAt309 : soko1_2.board.rollingTraps.contains 309 = false := by decide +kernel
theorem boxAt309 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 309 = false := rfl
theorem holeAt309 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 309 = false := rfl
theorem advanceAt309_north : advance soko1_2.board 309 .north = some 283 := by decide +kernel
theorem advanceAt309_south : advance soko1_2.board 309 .south = some 335 := by decide +kernel
theorem advanceAt309_east : advance soko1_2.board 309 .east = some 310 := by decide +kernel
theorem advanceAt309_west : advance soko1_2.board 309 .west = some 308 := by decide +kernel
theorem advanceAt309_northEast : advance soko1_2.board 309 .northEast = some 284 := by decide +kernel
theorem advanceAt309_northWest : advance soko1_2.board 309 .northWest = some 282 := by decide +kernel
theorem advanceAt309_southEast : advance soko1_2.board 309 .southEast = some 336 := by decide +kernel
theorem advanceAt309_southWest : advance soko1_2.board 309 .southWest = some 334 := by decide +kernel
theorem floorAt310 : soko1_2.board.floor.contains 310 = true := by decide +kernel
theorem doorAt310 : soko1_2.board.doors.contains 310 = false := by decide +kernel
theorem trapAt310 : soko1_2.board.rollingTraps.contains 310 = false := by decide +kernel
theorem boxAt310 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 310 = false := rfl
theorem holeAt310 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 310 = false := rfl
theorem advanceAt310_north : advance soko1_2.board 310 .north = some 284 := by decide +kernel
theorem advanceAt310_south : advance soko1_2.board 310 .south = some 336 := by decide +kernel
theorem advanceAt310_east : advance soko1_2.board 310 .east = some 311 := by decide +kernel
theorem advanceAt310_west : advance soko1_2.board 310 .west = some 309 := by decide +kernel
theorem advanceAt310_northEast : advance soko1_2.board 310 .northEast = some 285 := by decide +kernel
theorem advanceAt310_northWest : advance soko1_2.board 310 .northWest = some 283 := by decide +kernel
theorem advanceAt310_southEast : advance soko1_2.board 310 .southEast = some 337 := by decide +kernel
theorem advanceAt310_southWest : advance soko1_2.board 310 .southWest = some 335 := by decide +kernel
theorem floorAt311 : soko1_2.board.floor.contains 311 = false := by decide +kernel
theorem doorAt311 : soko1_2.board.doors.contains 311 = false := by decide +kernel
theorem trapAt311 : soko1_2.board.rollingTraps.contains 311 = false := by decide +kernel
theorem boxAt311 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 311 = false := rfl
theorem holeAt311 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 311 = false := rfl
theorem advanceAt311_north : advance soko1_2.board 311 .north = some 285 := by decide +kernel
theorem advanceAt311_south : advance soko1_2.board 311 .south = some 337 := by decide +kernel
theorem advanceAt311_east : advance soko1_2.board 311 .east = none := by decide +kernel
theorem advanceAt311_west : advance soko1_2.board 311 .west = some 310 := by decide +kernel
theorem advanceAt311_northEast : advance soko1_2.board 311 .northEast = none := by decide +kernel
theorem advanceAt311_northWest : advance soko1_2.board 311 .northWest = some 284 := by decide +kernel
theorem advanceAt311_southEast : advance soko1_2.board 311 .southEast = none := by decide +kernel
theorem advanceAt311_southWest : advance soko1_2.board 311 .southWest = some 336 := by decide +kernel
theorem floorAt312 : soko1_2.board.floor.contains 312 = false := by decide +kernel
theorem doorAt312 : soko1_2.board.doors.contains 312 = false := by decide +kernel
theorem trapAt312 : soko1_2.board.rollingTraps.contains 312 = false := by decide +kernel
theorem boxAt312 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 312 = false := rfl
theorem holeAt312 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 312 = false := rfl
theorem advanceAt312_north : advance soko1_2.board 312 .north = some 286 := by decide +kernel
theorem advanceAt312_south : advance soko1_2.board 312 .south = some 338 := by decide +kernel
theorem advanceAt312_east : advance soko1_2.board 312 .east = some 313 := by decide +kernel
theorem advanceAt312_west : advance soko1_2.board 312 .west = none := by decide +kernel
theorem advanceAt312_northEast : advance soko1_2.board 312 .northEast = some 287 := by decide +kernel
theorem advanceAt312_northWest : advance soko1_2.board 312 .northWest = none := by decide +kernel
theorem advanceAt312_southEast : advance soko1_2.board 312 .southEast = some 339 := by decide +kernel
theorem advanceAt312_southWest : advance soko1_2.board 312 .southWest = none := by decide +kernel
theorem floorAt313 : soko1_2.board.floor.contains 313 = false := by decide +kernel
theorem doorAt313 : soko1_2.board.doors.contains 313 = false := by decide +kernel
theorem trapAt313 : soko1_2.board.rollingTraps.contains 313 = false := by decide +kernel
theorem boxAt313 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 313 = false := rfl
theorem holeAt313 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 313 = false := rfl
theorem advanceAt313_north : advance soko1_2.board 313 .north = some 287 := by decide +kernel
theorem advanceAt313_south : advance soko1_2.board 313 .south = some 339 := by decide +kernel
theorem advanceAt313_east : advance soko1_2.board 313 .east = some 314 := by decide +kernel
theorem advanceAt313_west : advance soko1_2.board 313 .west = some 312 := by decide +kernel
theorem advanceAt313_northEast : advance soko1_2.board 313 .northEast = some 288 := by decide +kernel
theorem advanceAt313_northWest : advance soko1_2.board 313 .northWest = some 286 := by decide +kernel
theorem advanceAt313_southEast : advance soko1_2.board 313 .southEast = some 340 := by decide +kernel
theorem advanceAt313_southWest : advance soko1_2.board 313 .southWest = some 338 := by decide +kernel
theorem floorAt314 : soko1_2.board.floor.contains 314 = false := by decide +kernel
theorem doorAt314 : soko1_2.board.doors.contains 314 = false := by decide +kernel
theorem trapAt314 : soko1_2.board.rollingTraps.contains 314 = false := by decide +kernel
theorem boxAt314 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 314 = false := rfl
theorem holeAt314 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 314 = false := rfl
theorem advanceAt314_north : advance soko1_2.board 314 .north = some 288 := by decide +kernel
theorem advanceAt314_south : advance soko1_2.board 314 .south = some 340 := by decide +kernel
theorem advanceAt314_east : advance soko1_2.board 314 .east = some 315 := by decide +kernel
theorem advanceAt314_west : advance soko1_2.board 314 .west = some 313 := by decide +kernel
theorem advanceAt314_northEast : advance soko1_2.board 314 .northEast = some 289 := by decide +kernel
theorem advanceAt314_northWest : advance soko1_2.board 314 .northWest = some 287 := by decide +kernel
theorem advanceAt314_southEast : advance soko1_2.board 314 .southEast = some 341 := by decide +kernel
theorem advanceAt314_southWest : advance soko1_2.board 314 .southWest = some 339 := by decide +kernel
theorem floorAt315 : soko1_2.board.floor.contains 315 = false := by decide +kernel
theorem doorAt315 : soko1_2.board.doors.contains 315 = false := by decide +kernel
theorem trapAt315 : soko1_2.board.rollingTraps.contains 315 = false := by decide +kernel
theorem boxAt315 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 315 = false := rfl
theorem holeAt315 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 315 = false := rfl
theorem advanceAt315_north : advance soko1_2.board 315 .north = some 289 := by decide +kernel
theorem advanceAt315_south : advance soko1_2.board 315 .south = some 341 := by decide +kernel
theorem advanceAt315_east : advance soko1_2.board 315 .east = some 316 := by decide +kernel
theorem advanceAt315_west : advance soko1_2.board 315 .west = some 314 := by decide +kernel
theorem advanceAt315_northEast : advance soko1_2.board 315 .northEast = some 290 := by decide +kernel
theorem advanceAt315_northWest : advance soko1_2.board 315 .northWest = some 288 := by decide +kernel
theorem advanceAt315_southEast : advance soko1_2.board 315 .southEast = some 342 := by decide +kernel
theorem advanceAt315_southWest : advance soko1_2.board 315 .southWest = some 340 := by decide +kernel
theorem floorAt316 : soko1_2.board.floor.contains 316 = false := by decide +kernel
theorem doorAt316 : soko1_2.board.doors.contains 316 = false := by decide +kernel
theorem trapAt316 : soko1_2.board.rollingTraps.contains 316 = false := by decide +kernel
theorem boxAt316 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 316 = false := rfl
theorem holeAt316 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 316 = false := rfl
theorem advanceAt316_north : advance soko1_2.board 316 .north = some 290 := by decide +kernel
theorem advanceAt316_south : advance soko1_2.board 316 .south = some 342 := by decide +kernel
theorem advanceAt316_east : advance soko1_2.board 316 .east = some 317 := by decide +kernel
theorem advanceAt316_west : advance soko1_2.board 316 .west = some 315 := by decide +kernel
theorem advanceAt316_northEast : advance soko1_2.board 316 .northEast = some 291 := by decide +kernel
theorem advanceAt316_northWest : advance soko1_2.board 316 .northWest = some 289 := by decide +kernel
theorem advanceAt316_southEast : advance soko1_2.board 316 .southEast = some 343 := by decide +kernel
theorem advanceAt316_southWest : advance soko1_2.board 316 .southWest = some 341 := by decide +kernel
theorem floorAt317 : soko1_2.board.floor.contains 317 = true := by decide +kernel
theorem doorAt317 : soko1_2.board.doors.contains 317 = false := by decide +kernel
theorem trapAt317 : soko1_2.board.rollingTraps.contains 317 = false := by decide +kernel
theorem boxAt317 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 317 = p 317 := rfl
theorem holeAt317 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 317 = false := rfl
theorem advanceAt317_north : advance soko1_2.board 317 .north = some 291 := by decide +kernel
theorem advanceAt317_south : advance soko1_2.board 317 .south = some 343 := by decide +kernel
theorem advanceAt317_east : advance soko1_2.board 317 .east = some 318 := by decide +kernel
theorem advanceAt317_west : advance soko1_2.board 317 .west = some 316 := by decide +kernel
theorem advanceAt317_northEast : advance soko1_2.board 317 .northEast = some 292 := by decide +kernel
theorem advanceAt317_northWest : advance soko1_2.board 317 .northWest = some 290 := by decide +kernel
theorem advanceAt317_southEast : advance soko1_2.board 317 .southEast = some 344 := by decide +kernel
theorem advanceAt317_southWest : advance soko1_2.board 317 .southWest = some 342 := by decide +kernel
theorem floorAt318 : soko1_2.board.floor.contains 318 = true := by decide +kernel
theorem doorAt318 : soko1_2.board.doors.contains 318 = false := by decide +kernel
theorem trapAt318 : soko1_2.board.rollingTraps.contains 318 = false := by decide +kernel
theorem boxAt318 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 318 = p 318 := rfl
theorem holeAt318 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 318 = false := rfl
theorem advanceAt318_north : advance soko1_2.board 318 .north = some 292 := by decide +kernel
theorem advanceAt318_south : advance soko1_2.board 318 .south = some 344 := by decide +kernel
theorem advanceAt318_east : advance soko1_2.board 318 .east = some 319 := by decide +kernel
theorem advanceAt318_west : advance soko1_2.board 318 .west = some 317 := by decide +kernel
theorem advanceAt318_northEast : advance soko1_2.board 318 .northEast = some 293 := by decide +kernel
theorem advanceAt318_northWest : advance soko1_2.board 318 .northWest = some 291 := by decide +kernel
theorem advanceAt318_southEast : advance soko1_2.board 318 .southEast = some 345 := by decide +kernel
theorem advanceAt318_southWest : advance soko1_2.board 318 .southWest = some 343 := by decide +kernel
theorem floorAt319 : soko1_2.board.floor.contains 319 = true := by decide +kernel
theorem doorAt319 : soko1_2.board.doors.contains 319 = false := by decide +kernel
theorem trapAt319 : soko1_2.board.rollingTraps.contains 319 = false := by decide +kernel
theorem boxAt319 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 319 = p 319 := rfl
theorem holeAt319 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 319 = false := rfl
theorem advanceAt319_north : advance soko1_2.board 319 .north = some 293 := by decide +kernel
theorem advanceAt319_south : advance soko1_2.board 319 .south = some 345 := by decide +kernel
theorem advanceAt319_east : advance soko1_2.board 319 .east = some 320 := by decide +kernel
theorem advanceAt319_west : advance soko1_2.board 319 .west = some 318 := by decide +kernel
theorem advanceAt319_northEast : advance soko1_2.board 319 .northEast = some 294 := by decide +kernel
theorem advanceAt319_northWest : advance soko1_2.board 319 .northWest = some 292 := by decide +kernel
theorem advanceAt319_southEast : advance soko1_2.board 319 .southEast = some 346 := by decide +kernel
theorem advanceAt319_southWest : advance soko1_2.board 319 .southWest = some 344 := by decide +kernel
end NetHack.Soko12Forward220.Unified.P05
