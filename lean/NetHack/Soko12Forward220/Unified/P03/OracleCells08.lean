import NetHack.Soko12Forward220.Unified.P03.OracleCells07
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P03
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem floorAt320 : soko1_2.board.floor.contains 320 = true := by decide +kernel
theorem doorAt320 : soko1_2.board.doors.contains 320 = false := by decide +kernel
theorem trapAt320 : soko1_2.board.rollingTraps.contains 320 = false := by decide +kernel
theorem boxAt320 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 320 = p 320 := rfl
theorem holeAt320 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 320 = false := rfl
theorem advanceAt320_north : advance soko1_2.board 320 .north = some 294 := by decide +kernel
theorem advanceAt320_south : advance soko1_2.board 320 .south = some 346 := by decide +kernel
theorem advanceAt320_east : advance soko1_2.board 320 .east = some 321 := by decide +kernel
theorem advanceAt320_west : advance soko1_2.board 320 .west = some 319 := by decide +kernel
theorem advanceAt320_northEast : advance soko1_2.board 320 .northEast = some 295 := by decide +kernel
theorem advanceAt320_northWest : advance soko1_2.board 320 .northWest = some 293 := by decide +kernel
theorem advanceAt320_southEast : advance soko1_2.board 320 .southEast = some 347 := by decide +kernel
theorem advanceAt320_southWest : advance soko1_2.board 320 .southWest = some 345 := by decide +kernel
theorem floorAt321 : soko1_2.board.floor.contains 321 = false := by decide +kernel
theorem doorAt321 : soko1_2.board.doors.contains 321 = false := by decide +kernel
theorem trapAt321 : soko1_2.board.rollingTraps.contains 321 = false := by decide +kernel
theorem boxAt321 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 321 = false := rfl
theorem holeAt321 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 321 = false := rfl
theorem advanceAt321_north : advance soko1_2.board 321 .north = some 295 := by decide +kernel
theorem advanceAt321_south : advance soko1_2.board 321 .south = some 347 := by decide +kernel
theorem advanceAt321_east : advance soko1_2.board 321 .east = some 322 := by decide +kernel
theorem advanceAt321_west : advance soko1_2.board 321 .west = some 320 := by decide +kernel
theorem advanceAt321_northEast : advance soko1_2.board 321 .northEast = some 296 := by decide +kernel
theorem advanceAt321_northWest : advance soko1_2.board 321 .northWest = some 294 := by decide +kernel
theorem advanceAt321_southEast : advance soko1_2.board 321 .southEast = some 348 := by decide +kernel
theorem advanceAt321_southWest : advance soko1_2.board 321 .southWest = some 346 := by decide +kernel
theorem floorAt322 : soko1_2.board.floor.contains 322 = true := by decide +kernel
theorem doorAt322 : soko1_2.board.doors.contains 322 = false := by decide +kernel
theorem trapAt322 : soko1_2.board.rollingTraps.contains 322 = false := by decide +kernel
theorem boxAt322 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 322 = p 322 := rfl
theorem holeAt322 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 322 = false := rfl
theorem advanceAt322_north : advance soko1_2.board 322 .north = some 296 := by decide +kernel
theorem advanceAt322_south : advance soko1_2.board 322 .south = some 348 := by decide +kernel
theorem advanceAt322_east : advance soko1_2.board 322 .east = some 323 := by decide +kernel
theorem advanceAt322_west : advance soko1_2.board 322 .west = some 321 := by decide +kernel
theorem advanceAt322_northEast : advance soko1_2.board 322 .northEast = some 297 := by decide +kernel
theorem advanceAt322_northWest : advance soko1_2.board 322 .northWest = some 295 := by decide +kernel
theorem advanceAt322_southEast : advance soko1_2.board 322 .southEast = some 349 := by decide +kernel
theorem advanceAt322_southWest : advance soko1_2.board 322 .southWest = some 347 := by decide +kernel
theorem floorAt323 : soko1_2.board.floor.contains 323 = false := by decide +kernel
theorem doorAt323 : soko1_2.board.doors.contains 323 = false := by decide +kernel
theorem trapAt323 : soko1_2.board.rollingTraps.contains 323 = false := by decide +kernel
theorem boxAt323 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 323 = false := rfl
theorem holeAt323 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 323 = false := rfl
theorem advanceAt323_north : advance soko1_2.board 323 .north = some 297 := by decide +kernel
theorem advanceAt323_south : advance soko1_2.board 323 .south = some 349 := by decide +kernel
theorem advanceAt323_east : advance soko1_2.board 323 .east = some 324 := by decide +kernel
theorem advanceAt323_west : advance soko1_2.board 323 .west = some 322 := by decide +kernel
theorem advanceAt323_northEast : advance soko1_2.board 323 .northEast = some 298 := by decide +kernel
theorem advanceAt323_northWest : advance soko1_2.board 323 .northWest = some 296 := by decide +kernel
theorem advanceAt323_southEast : advance soko1_2.board 323 .southEast = some 350 := by decide +kernel
theorem advanceAt323_southWest : advance soko1_2.board 323 .southWest = some 348 := by decide +kernel
theorem floorAt324 : soko1_2.board.floor.contains 324 = false := by decide +kernel
theorem doorAt324 : soko1_2.board.doors.contains 324 = false := by decide +kernel
theorem trapAt324 : soko1_2.board.rollingTraps.contains 324 = false := by decide +kernel
theorem boxAt324 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 324 = false := rfl
theorem holeAt324 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 324 = false := rfl
theorem advanceAt324_north : advance soko1_2.board 324 .north = some 298 := by decide +kernel
theorem advanceAt324_south : advance soko1_2.board 324 .south = some 350 := by decide +kernel
theorem advanceAt324_east : advance soko1_2.board 324 .east = some 325 := by decide +kernel
theorem advanceAt324_west : advance soko1_2.board 324 .west = some 323 := by decide +kernel
theorem advanceAt324_northEast : advance soko1_2.board 324 .northEast = some 299 := by decide +kernel
theorem advanceAt324_northWest : advance soko1_2.board 324 .northWest = some 297 := by decide +kernel
theorem advanceAt324_southEast : advance soko1_2.board 324 .southEast = some 351 := by decide +kernel
theorem advanceAt324_southWest : advance soko1_2.board 324 .southWest = some 349 := by decide +kernel
theorem floorAt325 : soko1_2.board.floor.contains 325 = false := by decide +kernel
theorem doorAt325 : soko1_2.board.doors.contains 325 = false := by decide +kernel
theorem trapAt325 : soko1_2.board.rollingTraps.contains 325 = false := by decide +kernel
theorem boxAt325 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 325 = false := rfl
theorem holeAt325 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 325 = false := rfl
theorem advanceAt325_north : advance soko1_2.board 325 .north = some 299 := by decide +kernel
theorem advanceAt325_south : advance soko1_2.board 325 .south = some 351 := by decide +kernel
theorem advanceAt325_east : advance soko1_2.board 325 .east = some 326 := by decide +kernel
theorem advanceAt325_west : advance soko1_2.board 325 .west = some 324 := by decide +kernel
theorem advanceAt325_northEast : advance soko1_2.board 325 .northEast = some 300 := by decide +kernel
theorem advanceAt325_northWest : advance soko1_2.board 325 .northWest = some 298 := by decide +kernel
theorem advanceAt325_southEast : advance soko1_2.board 325 .southEast = some 352 := by decide +kernel
theorem advanceAt325_southWest : advance soko1_2.board 325 .southWest = some 350 := by decide +kernel
theorem floorAt326 : soko1_2.board.floor.contains 326 = false := by decide +kernel
theorem doorAt326 : soko1_2.board.doors.contains 326 = false := by decide +kernel
theorem trapAt326 : soko1_2.board.rollingTraps.contains 326 = false := by decide +kernel
theorem boxAt326 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 326 = false := rfl
theorem holeAt326 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 326 = false := rfl
theorem advanceAt326_north : advance soko1_2.board 326 .north = some 300 := by decide +kernel
theorem advanceAt326_south : advance soko1_2.board 326 .south = some 352 := by decide +kernel
theorem advanceAt326_east : advance soko1_2.board 326 .east = some 327 := by decide +kernel
theorem advanceAt326_west : advance soko1_2.board 326 .west = some 325 := by decide +kernel
theorem advanceAt326_northEast : advance soko1_2.board 326 .northEast = some 301 := by decide +kernel
theorem advanceAt326_northWest : advance soko1_2.board 326 .northWest = some 299 := by decide +kernel
theorem advanceAt326_southEast : advance soko1_2.board 326 .southEast = some 353 := by decide +kernel
theorem advanceAt326_southWest : advance soko1_2.board 326 .southWest = some 351 := by decide +kernel
theorem floorAt327 : soko1_2.board.floor.contains 327 = false := by decide +kernel
theorem doorAt327 : soko1_2.board.doors.contains 327 = false := by decide +kernel
theorem trapAt327 : soko1_2.board.rollingTraps.contains 327 = false := by decide +kernel
theorem boxAt327 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 327 = false := rfl
theorem holeAt327 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 327 = false := rfl
theorem advanceAt327_north : advance soko1_2.board 327 .north = some 301 := by decide +kernel
theorem advanceAt327_south : advance soko1_2.board 327 .south = some 353 := by decide +kernel
theorem advanceAt327_east : advance soko1_2.board 327 .east = some 328 := by decide +kernel
theorem advanceAt327_west : advance soko1_2.board 327 .west = some 326 := by decide +kernel
theorem advanceAt327_northEast : advance soko1_2.board 327 .northEast = some 302 := by decide +kernel
theorem advanceAt327_northWest : advance soko1_2.board 327 .northWest = some 300 := by decide +kernel
theorem advanceAt327_southEast : advance soko1_2.board 327 .southEast = some 354 := by decide +kernel
theorem advanceAt327_southWest : advance soko1_2.board 327 .southWest = some 352 := by decide +kernel
theorem floorAt328 : soko1_2.board.floor.contains 328 = true := by decide +kernel
theorem doorAt328 : soko1_2.board.doors.contains 328 = false := by decide +kernel
theorem trapAt328 : soko1_2.board.rollingTraps.contains 328 = false := by decide +kernel
theorem boxAt328 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 328 = false := rfl
theorem holeAt328 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 328 = false := rfl
theorem advanceAt328_north : advance soko1_2.board 328 .north = some 302 := by decide +kernel
theorem advanceAt328_south : advance soko1_2.board 328 .south = some 354 := by decide +kernel
theorem advanceAt328_east : advance soko1_2.board 328 .east = some 329 := by decide +kernel
theorem advanceAt328_west : advance soko1_2.board 328 .west = some 327 := by decide +kernel
theorem advanceAt328_northEast : advance soko1_2.board 328 .northEast = some 303 := by decide +kernel
theorem advanceAt328_northWest : advance soko1_2.board 328 .northWest = some 301 := by decide +kernel
theorem advanceAt328_southEast : advance soko1_2.board 328 .southEast = some 355 := by decide +kernel
theorem advanceAt328_southWest : advance soko1_2.board 328 .southWest = some 353 := by decide +kernel
theorem floorAt329 : soko1_2.board.floor.contains 329 = false := by decide +kernel
theorem doorAt329 : soko1_2.board.doors.contains 329 = true := by decide +kernel
theorem trapAt329 : soko1_2.board.rollingTraps.contains 329 = false := by decide +kernel
theorem boxAt329 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 329 = false := rfl
theorem holeAt329 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 329 = false := rfl
theorem advanceAt329_north : advance soko1_2.board 329 .north = some 303 := by decide +kernel
theorem advanceAt329_south : advance soko1_2.board 329 .south = some 355 := by decide +kernel
theorem advanceAt329_east : advance soko1_2.board 329 .east = some 330 := by decide +kernel
theorem advanceAt329_west : advance soko1_2.board 329 .west = some 328 := by decide +kernel
theorem advanceAt329_northEast : advance soko1_2.board 329 .northEast = some 304 := by decide +kernel
theorem advanceAt329_northWest : advance soko1_2.board 329 .northWest = some 302 := by decide +kernel
theorem advanceAt329_southEast : advance soko1_2.board 329 .southEast = some 356 := by decide +kernel
theorem advanceAt329_southWest : advance soko1_2.board 329 .southWest = some 354 := by decide +kernel
theorem floorAt330 : soko1_2.board.floor.contains 330 = true := by decide +kernel
theorem doorAt330 : soko1_2.board.doors.contains 330 = false := by decide +kernel
theorem trapAt330 : soko1_2.board.rollingTraps.contains 330 = false := by decide +kernel
theorem boxAt330 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 330 = false := rfl
theorem holeAt330 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 330 = false := rfl
theorem advanceAt330_north : advance soko1_2.board 330 .north = some 304 := by decide +kernel
theorem advanceAt330_south : advance soko1_2.board 330 .south = some 356 := by decide +kernel
theorem advanceAt330_east : advance soko1_2.board 330 .east = some 331 := by decide +kernel
theorem advanceAt330_west : advance soko1_2.board 330 .west = some 329 := by decide +kernel
theorem advanceAt330_northEast : advance soko1_2.board 330 .northEast = some 305 := by decide +kernel
theorem advanceAt330_northWest : advance soko1_2.board 330 .northWest = some 303 := by decide +kernel
theorem advanceAt330_southEast : advance soko1_2.board 330 .southEast = some 357 := by decide +kernel
theorem advanceAt330_southWest : advance soko1_2.board 330 .southWest = some 355 := by decide +kernel
theorem floorAt331 : soko1_2.board.floor.contains 331 = true := by decide +kernel
theorem doorAt331 : soko1_2.board.doors.contains 331 = false := by decide +kernel
theorem trapAt331 : soko1_2.board.rollingTraps.contains 331 = false := by decide +kernel
theorem boxAt331 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 331 = false := rfl
theorem holeAt331 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 331 = false := rfl
theorem advanceAt331_north : advance soko1_2.board 331 .north = some 305 := by decide +kernel
theorem advanceAt331_south : advance soko1_2.board 331 .south = some 357 := by decide +kernel
theorem advanceAt331_east : advance soko1_2.board 331 .east = some 332 := by decide +kernel
theorem advanceAt331_west : advance soko1_2.board 331 .west = some 330 := by decide +kernel
theorem advanceAt331_northEast : advance soko1_2.board 331 .northEast = some 306 := by decide +kernel
theorem advanceAt331_northWest : advance soko1_2.board 331 .northWest = some 304 := by decide +kernel
theorem advanceAt331_southEast : advance soko1_2.board 331 .southEast = some 358 := by decide +kernel
theorem advanceAt331_southWest : advance soko1_2.board 331 .southWest = some 356 := by decide +kernel
theorem floorAt332 : soko1_2.board.floor.contains 332 = true := by decide +kernel
theorem doorAt332 : soko1_2.board.doors.contains 332 = false := by decide +kernel
theorem trapAt332 : soko1_2.board.rollingTraps.contains 332 = false := by decide +kernel
theorem boxAt332 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 332 = false := rfl
theorem holeAt332 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 332 = false := rfl
theorem advanceAt332_north : advance soko1_2.board 332 .north = some 306 := by decide +kernel
theorem advanceAt332_south : advance soko1_2.board 332 .south = some 358 := by decide +kernel
theorem advanceAt332_east : advance soko1_2.board 332 .east = some 333 := by decide +kernel
theorem advanceAt332_west : advance soko1_2.board 332 .west = some 331 := by decide +kernel
theorem advanceAt332_northEast : advance soko1_2.board 332 .northEast = some 307 := by decide +kernel
theorem advanceAt332_northWest : advance soko1_2.board 332 .northWest = some 305 := by decide +kernel
theorem advanceAt332_southEast : advance soko1_2.board 332 .southEast = some 359 := by decide +kernel
theorem advanceAt332_southWest : advance soko1_2.board 332 .southWest = some 357 := by decide +kernel
theorem floorAt333 : soko1_2.board.floor.contains 333 = true := by decide +kernel
theorem doorAt333 : soko1_2.board.doors.contains 333 = false := by decide +kernel
theorem trapAt333 : soko1_2.board.rollingTraps.contains 333 = false := by decide +kernel
theorem boxAt333 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 333 = false := rfl
theorem holeAt333 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 333 = false := rfl
theorem advanceAt333_north : advance soko1_2.board 333 .north = some 307 := by decide +kernel
theorem advanceAt333_south : advance soko1_2.board 333 .south = some 359 := by decide +kernel
theorem advanceAt333_east : advance soko1_2.board 333 .east = some 334 := by decide +kernel
theorem advanceAt333_west : advance soko1_2.board 333 .west = some 332 := by decide +kernel
theorem advanceAt333_northEast : advance soko1_2.board 333 .northEast = some 308 := by decide +kernel
theorem advanceAt333_northWest : advance soko1_2.board 333 .northWest = some 306 := by decide +kernel
theorem advanceAt333_southEast : advance soko1_2.board 333 .southEast = some 360 := by decide +kernel
theorem advanceAt333_southWest : advance soko1_2.board 333 .southWest = some 358 := by decide +kernel
theorem floorAt334 : soko1_2.board.floor.contains 334 = true := by decide +kernel
theorem doorAt334 : soko1_2.board.doors.contains 334 = false := by decide +kernel
theorem trapAt334 : soko1_2.board.rollingTraps.contains 334 = false := by decide +kernel
theorem boxAt334 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 334 = false := rfl
theorem holeAt334 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 334 = false := rfl
theorem advanceAt334_north : advance soko1_2.board 334 .north = some 308 := by decide +kernel
theorem advanceAt334_south : advance soko1_2.board 334 .south = some 360 := by decide +kernel
theorem advanceAt334_east : advance soko1_2.board 334 .east = some 335 := by decide +kernel
theorem advanceAt334_west : advance soko1_2.board 334 .west = some 333 := by decide +kernel
theorem advanceAt334_northEast : advance soko1_2.board 334 .northEast = some 309 := by decide +kernel
theorem advanceAt334_northWest : advance soko1_2.board 334 .northWest = some 307 := by decide +kernel
theorem advanceAt334_southEast : advance soko1_2.board 334 .southEast = some 361 := by decide +kernel
theorem advanceAt334_southWest : advance soko1_2.board 334 .southWest = some 359 := by decide +kernel
theorem floorAt335 : soko1_2.board.floor.contains 335 = false := by decide +kernel
theorem doorAt335 : soko1_2.board.doors.contains 335 = true := by decide +kernel
theorem trapAt335 : soko1_2.board.rollingTraps.contains 335 = false := by decide +kernel
theorem boxAt335 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 335 = false := rfl
theorem holeAt335 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 335 = false := rfl
theorem advanceAt335_north : advance soko1_2.board 335 .north = some 309 := by decide +kernel
theorem advanceAt335_south : advance soko1_2.board 335 .south = some 361 := by decide +kernel
theorem advanceAt335_east : advance soko1_2.board 335 .east = some 336 := by decide +kernel
theorem advanceAt335_west : advance soko1_2.board 335 .west = some 334 := by decide +kernel
theorem advanceAt335_northEast : advance soko1_2.board 335 .northEast = some 310 := by decide +kernel
theorem advanceAt335_northWest : advance soko1_2.board 335 .northWest = some 308 := by decide +kernel
theorem advanceAt335_southEast : advance soko1_2.board 335 .southEast = some 362 := by decide +kernel
theorem advanceAt335_southWest : advance soko1_2.board 335 .southWest = some 360 := by decide +kernel
theorem floorAt336 : soko1_2.board.floor.contains 336 = true := by decide +kernel
theorem doorAt336 : soko1_2.board.doors.contains 336 = false := by decide +kernel
theorem trapAt336 : soko1_2.board.rollingTraps.contains 336 = false := by decide +kernel
theorem boxAt336 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 336 = false := rfl
theorem holeAt336 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 336 = false := rfl
theorem advanceAt336_north : advance soko1_2.board 336 .north = some 310 := by decide +kernel
theorem advanceAt336_south : advance soko1_2.board 336 .south = some 362 := by decide +kernel
theorem advanceAt336_east : advance soko1_2.board 336 .east = some 337 := by decide +kernel
theorem advanceAt336_west : advance soko1_2.board 336 .west = some 335 := by decide +kernel
theorem advanceAt336_northEast : advance soko1_2.board 336 .northEast = some 311 := by decide +kernel
theorem advanceAt336_northWest : advance soko1_2.board 336 .northWest = some 309 := by decide +kernel
theorem advanceAt336_southEast : advance soko1_2.board 336 .southEast = some 363 := by decide +kernel
theorem advanceAt336_southWest : advance soko1_2.board 336 .southWest = some 361 := by decide +kernel
theorem floorAt337 : soko1_2.board.floor.contains 337 = false := by decide +kernel
theorem doorAt337 : soko1_2.board.doors.contains 337 = false := by decide +kernel
theorem trapAt337 : soko1_2.board.rollingTraps.contains 337 = false := by decide +kernel
theorem boxAt337 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 337 = false := rfl
theorem holeAt337 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 337 = false := rfl
theorem advanceAt337_north : advance soko1_2.board 337 .north = some 311 := by decide +kernel
theorem advanceAt337_south : advance soko1_2.board 337 .south = some 363 := by decide +kernel
theorem advanceAt337_east : advance soko1_2.board 337 .east = none := by decide +kernel
theorem advanceAt337_west : advance soko1_2.board 337 .west = some 336 := by decide +kernel
theorem advanceAt337_northEast : advance soko1_2.board 337 .northEast = none := by decide +kernel
theorem advanceAt337_northWest : advance soko1_2.board 337 .northWest = some 310 := by decide +kernel
theorem advanceAt337_southEast : advance soko1_2.board 337 .southEast = none := by decide +kernel
theorem advanceAt337_southWest : advance soko1_2.board 337 .southWest = some 362 := by decide +kernel
theorem floorAt338 : soko1_2.board.floor.contains 338 = false := by decide +kernel
theorem doorAt338 : soko1_2.board.doors.contains 338 = false := by decide +kernel
theorem trapAt338 : soko1_2.board.rollingTraps.contains 338 = false := by decide +kernel
theorem boxAt338 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 338 = false := rfl
theorem holeAt338 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 338 = false := rfl
theorem advanceAt338_north : advance soko1_2.board 338 .north = some 312 := by decide +kernel
theorem advanceAt338_south : advance soko1_2.board 338 .south = some 364 := by decide +kernel
theorem advanceAt338_east : advance soko1_2.board 338 .east = some 339 := by decide +kernel
theorem advanceAt338_west : advance soko1_2.board 338 .west = none := by decide +kernel
theorem advanceAt338_northEast : advance soko1_2.board 338 .northEast = some 313 := by decide +kernel
theorem advanceAt338_northWest : advance soko1_2.board 338 .northWest = none := by decide +kernel
theorem advanceAt338_southEast : advance soko1_2.board 338 .southEast = some 365 := by decide +kernel
theorem advanceAt338_southWest : advance soko1_2.board 338 .southWest = none := by decide +kernel
theorem floorAt339 : soko1_2.board.floor.contains 339 = false := by decide +kernel
theorem doorAt339 : soko1_2.board.doors.contains 339 = false := by decide +kernel
theorem trapAt339 : soko1_2.board.rollingTraps.contains 339 = false := by decide +kernel
theorem boxAt339 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 339 = false := rfl
theorem holeAt339 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 339 = false := rfl
theorem advanceAt339_north : advance soko1_2.board 339 .north = some 313 := by decide +kernel
theorem advanceAt339_south : advance soko1_2.board 339 .south = some 365 := by decide +kernel
theorem advanceAt339_east : advance soko1_2.board 339 .east = some 340 := by decide +kernel
theorem advanceAt339_west : advance soko1_2.board 339 .west = some 338 := by decide +kernel
theorem advanceAt339_northEast : advance soko1_2.board 339 .northEast = some 314 := by decide +kernel
theorem advanceAt339_northWest : advance soko1_2.board 339 .northWest = some 312 := by decide +kernel
theorem advanceAt339_southEast : advance soko1_2.board 339 .southEast = some 366 := by decide +kernel
theorem advanceAt339_southWest : advance soko1_2.board 339 .southWest = some 364 := by decide +kernel
theorem floorAt340 : soko1_2.board.floor.contains 340 = false := by decide +kernel
theorem doorAt340 : soko1_2.board.doors.contains 340 = false := by decide +kernel
theorem trapAt340 : soko1_2.board.rollingTraps.contains 340 = false := by decide +kernel
theorem boxAt340 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 340 = false := rfl
theorem holeAt340 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 340 = false := rfl
theorem advanceAt340_north : advance soko1_2.board 340 .north = some 314 := by decide +kernel
theorem advanceAt340_south : advance soko1_2.board 340 .south = some 366 := by decide +kernel
theorem advanceAt340_east : advance soko1_2.board 340 .east = some 341 := by decide +kernel
theorem advanceAt340_west : advance soko1_2.board 340 .west = some 339 := by decide +kernel
theorem advanceAt340_northEast : advance soko1_2.board 340 .northEast = some 315 := by decide +kernel
theorem advanceAt340_northWest : advance soko1_2.board 340 .northWest = some 313 := by decide +kernel
theorem advanceAt340_southEast : advance soko1_2.board 340 .southEast = some 367 := by decide +kernel
theorem advanceAt340_southWest : advance soko1_2.board 340 .southWest = some 365 := by decide +kernel
theorem floorAt341 : soko1_2.board.floor.contains 341 = false := by decide +kernel
theorem doorAt341 : soko1_2.board.doors.contains 341 = false := by decide +kernel
theorem trapAt341 : soko1_2.board.rollingTraps.contains 341 = false := by decide +kernel
theorem boxAt341 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 341 = false := rfl
theorem holeAt341 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 341 = false := rfl
theorem advanceAt341_north : advance soko1_2.board 341 .north = some 315 := by decide +kernel
theorem advanceAt341_south : advance soko1_2.board 341 .south = some 367 := by decide +kernel
theorem advanceAt341_east : advance soko1_2.board 341 .east = some 342 := by decide +kernel
theorem advanceAt341_west : advance soko1_2.board 341 .west = some 340 := by decide +kernel
theorem advanceAt341_northEast : advance soko1_2.board 341 .northEast = some 316 := by decide +kernel
theorem advanceAt341_northWest : advance soko1_2.board 341 .northWest = some 314 := by decide +kernel
theorem advanceAt341_southEast : advance soko1_2.board 341 .southEast = some 368 := by decide +kernel
theorem advanceAt341_southWest : advance soko1_2.board 341 .southWest = some 366 := by decide +kernel
theorem floorAt342 : soko1_2.board.floor.contains 342 = false := by decide +kernel
theorem doorAt342 : soko1_2.board.doors.contains 342 = false := by decide +kernel
theorem trapAt342 : soko1_2.board.rollingTraps.contains 342 = false := by decide +kernel
theorem boxAt342 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 342 = false := rfl
theorem holeAt342 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 342 = false := rfl
theorem advanceAt342_north : advance soko1_2.board 342 .north = some 316 := by decide +kernel
theorem advanceAt342_south : advance soko1_2.board 342 .south = some 368 := by decide +kernel
theorem advanceAt342_east : advance soko1_2.board 342 .east = some 343 := by decide +kernel
theorem advanceAt342_west : advance soko1_2.board 342 .west = some 341 := by decide +kernel
theorem advanceAt342_northEast : advance soko1_2.board 342 .northEast = some 317 := by decide +kernel
theorem advanceAt342_northWest : advance soko1_2.board 342 .northWest = some 315 := by decide +kernel
theorem advanceAt342_southEast : advance soko1_2.board 342 .southEast = some 369 := by decide +kernel
theorem advanceAt342_southWest : advance soko1_2.board 342 .southWest = some 367 := by decide +kernel
theorem floorAt343 : soko1_2.board.floor.contains 343 = false := by decide +kernel
theorem doorAt343 : soko1_2.board.doors.contains 343 = false := by decide +kernel
theorem trapAt343 : soko1_2.board.rollingTraps.contains 343 = false := by decide +kernel
theorem boxAt343 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 343 = false := rfl
theorem holeAt343 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 343 = false := rfl
theorem advanceAt343_north : advance soko1_2.board 343 .north = some 317 := by decide +kernel
theorem advanceAt343_south : advance soko1_2.board 343 .south = some 369 := by decide +kernel
theorem advanceAt343_east : advance soko1_2.board 343 .east = some 344 := by decide +kernel
theorem advanceAt343_west : advance soko1_2.board 343 .west = some 342 := by decide +kernel
theorem advanceAt343_northEast : advance soko1_2.board 343 .northEast = some 318 := by decide +kernel
theorem advanceAt343_northWest : advance soko1_2.board 343 .northWest = some 316 := by decide +kernel
theorem advanceAt343_southEast : advance soko1_2.board 343 .southEast = some 370 := by decide +kernel
theorem advanceAt343_southWest : advance soko1_2.board 343 .southWest = some 368 := by decide +kernel
theorem floorAt344 : soko1_2.board.floor.contains 344 = false := by decide +kernel
theorem doorAt344 : soko1_2.board.doors.contains 344 = false := by decide +kernel
theorem trapAt344 : soko1_2.board.rollingTraps.contains 344 = false := by decide +kernel
theorem boxAt344 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 344 = false := rfl
theorem holeAt344 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 344 = false := rfl
theorem advanceAt344_north : advance soko1_2.board 344 .north = some 318 := by decide +kernel
theorem advanceAt344_south : advance soko1_2.board 344 .south = some 370 := by decide +kernel
theorem advanceAt344_east : advance soko1_2.board 344 .east = some 345 := by decide +kernel
theorem advanceAt344_west : advance soko1_2.board 344 .west = some 343 := by decide +kernel
theorem advanceAt344_northEast : advance soko1_2.board 344 .northEast = some 319 := by decide +kernel
theorem advanceAt344_northWest : advance soko1_2.board 344 .northWest = some 317 := by decide +kernel
theorem advanceAt344_southEast : advance soko1_2.board 344 .southEast = some 371 := by decide +kernel
theorem advanceAt344_southWest : advance soko1_2.board 344 .southWest = some 369 := by decide +kernel
theorem floorAt345 : soko1_2.board.floor.contains 345 = true := by decide +kernel
theorem doorAt345 : soko1_2.board.doors.contains 345 = false := by decide +kernel
theorem trapAt345 : soko1_2.board.rollingTraps.contains 345 = false := by decide +kernel
theorem boxAt345 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 345 = p 345 := rfl
theorem holeAt345 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 345 = false := rfl
theorem advanceAt345_north : advance soko1_2.board 345 .north = some 319 := by decide +kernel
theorem advanceAt345_south : advance soko1_2.board 345 .south = some 371 := by decide +kernel
theorem advanceAt345_east : advance soko1_2.board 345 .east = some 346 := by decide +kernel
theorem advanceAt345_west : advance soko1_2.board 345 .west = some 344 := by decide +kernel
theorem advanceAt345_northEast : advance soko1_2.board 345 .northEast = some 320 := by decide +kernel
theorem advanceAt345_northWest : advance soko1_2.board 345 .northWest = some 318 := by decide +kernel
theorem advanceAt345_southEast : advance soko1_2.board 345 .southEast = some 372 := by decide +kernel
theorem advanceAt345_southWest : advance soko1_2.board 345 .southWest = some 370 := by decide +kernel
theorem floorAt346 : soko1_2.board.floor.contains 346 = false := by decide +kernel
theorem doorAt346 : soko1_2.board.doors.contains 346 = false := by decide +kernel
theorem trapAt346 : soko1_2.board.rollingTraps.contains 346 = false := by decide +kernel
theorem boxAt346 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 346 = false := rfl
theorem holeAt346 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 346 = false := rfl
theorem advanceAt346_north : advance soko1_2.board 346 .north = some 320 := by decide +kernel
theorem advanceAt346_south : advance soko1_2.board 346 .south = some 372 := by decide +kernel
theorem advanceAt346_east : advance soko1_2.board 346 .east = some 347 := by decide +kernel
theorem advanceAt346_west : advance soko1_2.board 346 .west = some 345 := by decide +kernel
theorem advanceAt346_northEast : advance soko1_2.board 346 .northEast = some 321 := by decide +kernel
theorem advanceAt346_northWest : advance soko1_2.board 346 .northWest = some 319 := by decide +kernel
theorem advanceAt346_southEast : advance soko1_2.board 346 .southEast = some 373 := by decide +kernel
theorem advanceAt346_southWest : advance soko1_2.board 346 .southWest = some 371 := by decide +kernel
theorem floorAt347 : soko1_2.board.floor.contains 347 = false := by decide +kernel
theorem doorAt347 : soko1_2.board.doors.contains 347 = false := by decide +kernel
theorem trapAt347 : soko1_2.board.rollingTraps.contains 347 = false := by decide +kernel
theorem boxAt347 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 347 = false := rfl
theorem holeAt347 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 347 = false := rfl
theorem advanceAt347_north : advance soko1_2.board 347 .north = some 321 := by decide +kernel
theorem advanceAt347_south : advance soko1_2.board 347 .south = some 373 := by decide +kernel
theorem advanceAt347_east : advance soko1_2.board 347 .east = some 348 := by decide +kernel
theorem advanceAt347_west : advance soko1_2.board 347 .west = some 346 := by decide +kernel
theorem advanceAt347_northEast : advance soko1_2.board 347 .northEast = some 322 := by decide +kernel
theorem advanceAt347_northWest : advance soko1_2.board 347 .northWest = some 320 := by decide +kernel
theorem advanceAt347_southEast : advance soko1_2.board 347 .southEast = some 374 := by decide +kernel
theorem advanceAt347_southWest : advance soko1_2.board 347 .southWest = some 372 := by decide +kernel
theorem floorAt348 : soko1_2.board.floor.contains 348 = true := by decide +kernel
theorem doorAt348 : soko1_2.board.doors.contains 348 = false := by decide +kernel
theorem trapAt348 : soko1_2.board.rollingTraps.contains 348 = false := by decide +kernel
theorem boxAt348 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 348 = p 348 := rfl
theorem holeAt348 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 348 = false := rfl
theorem advanceAt348_north : advance soko1_2.board 348 .north = some 322 := by decide +kernel
theorem advanceAt348_south : advance soko1_2.board 348 .south = some 374 := by decide +kernel
theorem advanceAt348_east : advance soko1_2.board 348 .east = some 349 := by decide +kernel
theorem advanceAt348_west : advance soko1_2.board 348 .west = some 347 := by decide +kernel
theorem advanceAt348_northEast : advance soko1_2.board 348 .northEast = some 323 := by decide +kernel
theorem advanceAt348_northWest : advance soko1_2.board 348 .northWest = some 321 := by decide +kernel
theorem advanceAt348_southEast : advance soko1_2.board 348 .southEast = some 375 := by decide +kernel
theorem advanceAt348_southWest : advance soko1_2.board 348 .southWest = some 373 := by decide +kernel
theorem floorAt349 : soko1_2.board.floor.contains 349 = false := by decide +kernel
theorem doorAt349 : soko1_2.board.doors.contains 349 = false := by decide +kernel
theorem trapAt349 : soko1_2.board.rollingTraps.contains 349 = false := by decide +kernel
theorem boxAt349 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 349 = false := rfl
theorem holeAt349 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 349 = false := rfl
theorem advanceAt349_north : advance soko1_2.board 349 .north = some 323 := by decide +kernel
theorem advanceAt349_south : advance soko1_2.board 349 .south = some 375 := by decide +kernel
theorem advanceAt349_east : advance soko1_2.board 349 .east = some 350 := by decide +kernel
theorem advanceAt349_west : advance soko1_2.board 349 .west = some 348 := by decide +kernel
theorem advanceAt349_northEast : advance soko1_2.board 349 .northEast = some 324 := by decide +kernel
theorem advanceAt349_northWest : advance soko1_2.board 349 .northWest = some 322 := by decide +kernel
theorem advanceAt349_southEast : advance soko1_2.board 349 .southEast = some 376 := by decide +kernel
theorem advanceAt349_southWest : advance soko1_2.board 349 .southWest = some 374 := by decide +kernel
theorem floorAt350 : soko1_2.board.floor.contains 350 = false := by decide +kernel
theorem doorAt350 : soko1_2.board.doors.contains 350 = false := by decide +kernel
theorem trapAt350 : soko1_2.board.rollingTraps.contains 350 = false := by decide +kernel
theorem boxAt350 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 350 = false := rfl
theorem holeAt350 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 350 = false := rfl
theorem advanceAt350_north : advance soko1_2.board 350 .north = some 324 := by decide +kernel
theorem advanceAt350_south : advance soko1_2.board 350 .south = some 376 := by decide +kernel
theorem advanceAt350_east : advance soko1_2.board 350 .east = some 351 := by decide +kernel
theorem advanceAt350_west : advance soko1_2.board 350 .west = some 349 := by decide +kernel
theorem advanceAt350_northEast : advance soko1_2.board 350 .northEast = some 325 := by decide +kernel
theorem advanceAt350_northWest : advance soko1_2.board 350 .northWest = some 323 := by decide +kernel
theorem advanceAt350_southEast : advance soko1_2.board 350 .southEast = some 377 := by decide +kernel
theorem advanceAt350_southWest : advance soko1_2.board 350 .southWest = some 375 := by decide +kernel
theorem floorAt351 : soko1_2.board.floor.contains 351 = false := by decide +kernel
theorem doorAt351 : soko1_2.board.doors.contains 351 = false := by decide +kernel
theorem trapAt351 : soko1_2.board.rollingTraps.contains 351 = false := by decide +kernel
theorem boxAt351 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 351 = false := rfl
theorem holeAt351 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 351 = false := rfl
theorem advanceAt351_north : advance soko1_2.board 351 .north = some 325 := by decide +kernel
theorem advanceAt351_south : advance soko1_2.board 351 .south = some 377 := by decide +kernel
theorem advanceAt351_east : advance soko1_2.board 351 .east = some 352 := by decide +kernel
theorem advanceAt351_west : advance soko1_2.board 351 .west = some 350 := by decide +kernel
theorem advanceAt351_northEast : advance soko1_2.board 351 .northEast = some 326 := by decide +kernel
theorem advanceAt351_northWest : advance soko1_2.board 351 .northWest = some 324 := by decide +kernel
theorem advanceAt351_southEast : advance soko1_2.board 351 .southEast = some 378 := by decide +kernel
theorem advanceAt351_southWest : advance soko1_2.board 351 .southWest = some 376 := by decide +kernel
theorem floorAt352 : soko1_2.board.floor.contains 352 = false := by decide +kernel
theorem doorAt352 : soko1_2.board.doors.contains 352 = false := by decide +kernel
theorem trapAt352 : soko1_2.board.rollingTraps.contains 352 = false := by decide +kernel
theorem boxAt352 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 352 = false := rfl
theorem holeAt352 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 352 = false := rfl
theorem advanceAt352_north : advance soko1_2.board 352 .north = some 326 := by decide +kernel
theorem advanceAt352_south : advance soko1_2.board 352 .south = some 378 := by decide +kernel
theorem advanceAt352_east : advance soko1_2.board 352 .east = some 353 := by decide +kernel
theorem advanceAt352_west : advance soko1_2.board 352 .west = some 351 := by decide +kernel
theorem advanceAt352_northEast : advance soko1_2.board 352 .northEast = some 327 := by decide +kernel
theorem advanceAt352_northWest : advance soko1_2.board 352 .northWest = some 325 := by decide +kernel
theorem advanceAt352_southEast : advance soko1_2.board 352 .southEast = some 379 := by decide +kernel
theorem advanceAt352_southWest : advance soko1_2.board 352 .southWest = some 377 := by decide +kernel
theorem floorAt353 : soko1_2.board.floor.contains 353 = false := by decide +kernel
theorem doorAt353 : soko1_2.board.doors.contains 353 = false := by decide +kernel
theorem trapAt353 : soko1_2.board.rollingTraps.contains 353 = false := by decide +kernel
theorem boxAt353 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 353 = false := rfl
theorem holeAt353 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 353 = false := rfl
theorem advanceAt353_north : advance soko1_2.board 353 .north = some 327 := by decide +kernel
theorem advanceAt353_south : advance soko1_2.board 353 .south = some 379 := by decide +kernel
theorem advanceAt353_east : advance soko1_2.board 353 .east = some 354 := by decide +kernel
theorem advanceAt353_west : advance soko1_2.board 353 .west = some 352 := by decide +kernel
theorem advanceAt353_northEast : advance soko1_2.board 353 .northEast = some 328 := by decide +kernel
theorem advanceAt353_northWest : advance soko1_2.board 353 .northWest = some 326 := by decide +kernel
theorem advanceAt353_southEast : advance soko1_2.board 353 .southEast = some 380 := by decide +kernel
theorem advanceAt353_southWest : advance soko1_2.board 353 .southWest = some 378 := by decide +kernel
theorem floorAt354 : soko1_2.board.floor.contains 354 = false := by decide +kernel
theorem doorAt354 : soko1_2.board.doors.contains 354 = false := by decide +kernel
theorem trapAt354 : soko1_2.board.rollingTraps.contains 354 = false := by decide +kernel
theorem boxAt354 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 354 = false := rfl
theorem holeAt354 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 354 = false := rfl
theorem advanceAt354_north : advance soko1_2.board 354 .north = some 328 := by decide +kernel
theorem advanceAt354_south : advance soko1_2.board 354 .south = some 380 := by decide +kernel
theorem advanceAt354_east : advance soko1_2.board 354 .east = some 355 := by decide +kernel
theorem advanceAt354_west : advance soko1_2.board 354 .west = some 353 := by decide +kernel
theorem advanceAt354_northEast : advance soko1_2.board 354 .northEast = some 329 := by decide +kernel
theorem advanceAt354_northWest : advance soko1_2.board 354 .northWest = some 327 := by decide +kernel
theorem advanceAt354_southEast : advance soko1_2.board 354 .southEast = some 381 := by decide +kernel
theorem advanceAt354_southWest : advance soko1_2.board 354 .southWest = some 379 := by decide +kernel
theorem floorAt355 : soko1_2.board.floor.contains 355 = false := by decide +kernel
theorem doorAt355 : soko1_2.board.doors.contains 355 = false := by decide +kernel
theorem trapAt355 : soko1_2.board.rollingTraps.contains 355 = false := by decide +kernel
theorem boxAt355 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 355 = false := rfl
theorem holeAt355 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 355 = false := rfl
theorem advanceAt355_north : advance soko1_2.board 355 .north = some 329 := by decide +kernel
theorem advanceAt355_south : advance soko1_2.board 355 .south = some 381 := by decide +kernel
theorem advanceAt355_east : advance soko1_2.board 355 .east = some 356 := by decide +kernel
theorem advanceAt355_west : advance soko1_2.board 355 .west = some 354 := by decide +kernel
theorem advanceAt355_northEast : advance soko1_2.board 355 .northEast = some 330 := by decide +kernel
theorem advanceAt355_northWest : advance soko1_2.board 355 .northWest = some 328 := by decide +kernel
theorem advanceAt355_southEast : advance soko1_2.board 355 .southEast = some 382 := by decide +kernel
theorem advanceAt355_southWest : advance soko1_2.board 355 .southWest = some 380 := by decide +kernel
theorem floorAt356 : soko1_2.board.floor.contains 356 = true := by decide +kernel
theorem doorAt356 : soko1_2.board.doors.contains 356 = false := by decide +kernel
theorem trapAt356 : soko1_2.board.rollingTraps.contains 356 = false := by decide +kernel
theorem boxAt356 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 356 = false := rfl
theorem holeAt356 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 356 = false := rfl
theorem advanceAt356_north : advance soko1_2.board 356 .north = some 330 := by decide +kernel
theorem advanceAt356_south : advance soko1_2.board 356 .south = some 382 := by decide +kernel
theorem advanceAt356_east : advance soko1_2.board 356 .east = some 357 := by decide +kernel
theorem advanceAt356_west : advance soko1_2.board 356 .west = some 355 := by decide +kernel
theorem advanceAt356_northEast : advance soko1_2.board 356 .northEast = some 331 := by decide +kernel
theorem advanceAt356_northWest : advance soko1_2.board 356 .northWest = some 329 := by decide +kernel
theorem advanceAt356_southEast : advance soko1_2.board 356 .southEast = some 383 := by decide +kernel
theorem advanceAt356_southWest : advance soko1_2.board 356 .southWest = some 381 := by decide +kernel
theorem floorAt357 : soko1_2.board.floor.contains 357 = true := by decide +kernel
theorem doorAt357 : soko1_2.board.doors.contains 357 = false := by decide +kernel
theorem trapAt357 : soko1_2.board.rollingTraps.contains 357 = false := by decide +kernel
theorem boxAt357 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 357 = false := rfl
theorem holeAt357 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 357 = false := rfl
theorem advanceAt357_north : advance soko1_2.board 357 .north = some 331 := by decide +kernel
theorem advanceAt357_south : advance soko1_2.board 357 .south = some 383 := by decide +kernel
theorem advanceAt357_east : advance soko1_2.board 357 .east = some 358 := by decide +kernel
theorem advanceAt357_west : advance soko1_2.board 357 .west = some 356 := by decide +kernel
theorem advanceAt357_northEast : advance soko1_2.board 357 .northEast = some 332 := by decide +kernel
theorem advanceAt357_northWest : advance soko1_2.board 357 .northWest = some 330 := by decide +kernel
theorem advanceAt357_southEast : advance soko1_2.board 357 .southEast = some 384 := by decide +kernel
theorem advanceAt357_southWest : advance soko1_2.board 357 .southWest = some 382 := by decide +kernel
theorem floorAt358 : soko1_2.board.floor.contains 358 = true := by decide +kernel
theorem doorAt358 : soko1_2.board.doors.contains 358 = false := by decide +kernel
theorem trapAt358 : soko1_2.board.rollingTraps.contains 358 = false := by decide +kernel
theorem boxAt358 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 358 = false := rfl
theorem holeAt358 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 358 = false := rfl
theorem advanceAt358_north : advance soko1_2.board 358 .north = some 332 := by decide +kernel
theorem advanceAt358_south : advance soko1_2.board 358 .south = some 384 := by decide +kernel
theorem advanceAt358_east : advance soko1_2.board 358 .east = some 359 := by decide +kernel
theorem advanceAt358_west : advance soko1_2.board 358 .west = some 357 := by decide +kernel
theorem advanceAt358_northEast : advance soko1_2.board 358 .northEast = some 333 := by decide +kernel
theorem advanceAt358_northWest : advance soko1_2.board 358 .northWest = some 331 := by decide +kernel
theorem advanceAt358_southEast : advance soko1_2.board 358 .southEast = some 385 := by decide +kernel
theorem advanceAt358_southWest : advance soko1_2.board 358 .southWest = some 383 := by decide +kernel
theorem floorAt359 : soko1_2.board.floor.contains 359 = true := by decide +kernel
theorem doorAt359 : soko1_2.board.doors.contains 359 = false := by decide +kernel
theorem trapAt359 : soko1_2.board.rollingTraps.contains 359 = false := by decide +kernel
theorem boxAt359 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 359 = false := rfl
theorem holeAt359 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 359 = false := rfl
theorem advanceAt359_north : advance soko1_2.board 359 .north = some 333 := by decide +kernel
theorem advanceAt359_south : advance soko1_2.board 359 .south = some 385 := by decide +kernel
theorem advanceAt359_east : advance soko1_2.board 359 .east = some 360 := by decide +kernel
theorem advanceAt359_west : advance soko1_2.board 359 .west = some 358 := by decide +kernel
theorem advanceAt359_northEast : advance soko1_2.board 359 .northEast = some 334 := by decide +kernel
theorem advanceAt359_northWest : advance soko1_2.board 359 .northWest = some 332 := by decide +kernel
theorem advanceAt359_southEast : advance soko1_2.board 359 .southEast = some 386 := by decide +kernel
theorem advanceAt359_southWest : advance soko1_2.board 359 .southWest = some 384 := by decide +kernel
end NetHack.Soko12Forward220.Unified.P03
