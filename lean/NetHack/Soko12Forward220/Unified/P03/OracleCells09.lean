import NetHack.Soko12Forward220.Unified.P03.OracleCells08
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P03
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem floorAt360 : soko1_2.board.floor.contains 360 = true := by decide +kernel
theorem doorAt360 : soko1_2.board.doors.contains 360 = false := by decide +kernel
theorem trapAt360 : soko1_2.board.rollingTraps.contains 360 = false := by decide +kernel
theorem boxAt360 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 360 = false := rfl
theorem holeAt360 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 360 = false := rfl
theorem advanceAt360_north : advance soko1_2.board 360 .north = some 334 := by decide +kernel
theorem advanceAt360_south : advance soko1_2.board 360 .south = some 386 := by decide +kernel
theorem advanceAt360_east : advance soko1_2.board 360 .east = some 361 := by decide +kernel
theorem advanceAt360_west : advance soko1_2.board 360 .west = some 359 := by decide +kernel
theorem advanceAt360_northEast : advance soko1_2.board 360 .northEast = some 335 := by decide +kernel
theorem advanceAt360_northWest : advance soko1_2.board 360 .northWest = some 333 := by decide +kernel
theorem advanceAt360_southEast : advance soko1_2.board 360 .southEast = some 387 := by decide +kernel
theorem advanceAt360_southWest : advance soko1_2.board 360 .southWest = some 385 := by decide +kernel
theorem floorAt361 : soko1_2.board.floor.contains 361 = false := by decide +kernel
theorem doorAt361 : soko1_2.board.doors.contains 361 = false := by decide +kernel
theorem trapAt361 : soko1_2.board.rollingTraps.contains 361 = false := by decide +kernel
theorem boxAt361 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 361 = false := rfl
theorem holeAt361 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 361 = false := rfl
theorem advanceAt361_north : advance soko1_2.board 361 .north = some 335 := by decide +kernel
theorem advanceAt361_south : advance soko1_2.board 361 .south = some 387 := by decide +kernel
theorem advanceAt361_east : advance soko1_2.board 361 .east = some 362 := by decide +kernel
theorem advanceAt361_west : advance soko1_2.board 361 .west = some 360 := by decide +kernel
theorem advanceAt361_northEast : advance soko1_2.board 361 .northEast = some 336 := by decide +kernel
theorem advanceAt361_northWest : advance soko1_2.board 361 .northWest = some 334 := by decide +kernel
theorem advanceAt361_southEast : advance soko1_2.board 361 .southEast = some 388 := by decide +kernel
theorem advanceAt361_southWest : advance soko1_2.board 361 .southWest = some 386 := by decide +kernel
theorem floorAt362 : soko1_2.board.floor.contains 362 = false := by decide +kernel
theorem doorAt362 : soko1_2.board.doors.contains 362 = false := by decide +kernel
theorem trapAt362 : soko1_2.board.rollingTraps.contains 362 = false := by decide +kernel
theorem boxAt362 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 362 = false := rfl
theorem holeAt362 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 362 = false := rfl
theorem advanceAt362_north : advance soko1_2.board 362 .north = some 336 := by decide +kernel
theorem advanceAt362_south : advance soko1_2.board 362 .south = some 388 := by decide +kernel
theorem advanceAt362_east : advance soko1_2.board 362 .east = some 363 := by decide +kernel
theorem advanceAt362_west : advance soko1_2.board 362 .west = some 361 := by decide +kernel
theorem advanceAt362_northEast : advance soko1_2.board 362 .northEast = some 337 := by decide +kernel
theorem advanceAt362_northWest : advance soko1_2.board 362 .northWest = some 335 := by decide +kernel
theorem advanceAt362_southEast : advance soko1_2.board 362 .southEast = some 389 := by decide +kernel
theorem advanceAt362_southWest : advance soko1_2.board 362 .southWest = some 387 := by decide +kernel
theorem floorAt363 : soko1_2.board.floor.contains 363 = false := by decide +kernel
theorem doorAt363 : soko1_2.board.doors.contains 363 = false := by decide +kernel
theorem trapAt363 : soko1_2.board.rollingTraps.contains 363 = false := by decide +kernel
theorem boxAt363 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 363 = false := rfl
theorem holeAt363 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 363 = false := rfl
theorem advanceAt363_north : advance soko1_2.board 363 .north = some 337 := by decide +kernel
theorem advanceAt363_south : advance soko1_2.board 363 .south = some 389 := by decide +kernel
theorem advanceAt363_east : advance soko1_2.board 363 .east = none := by decide +kernel
theorem advanceAt363_west : advance soko1_2.board 363 .west = some 362 := by decide +kernel
theorem advanceAt363_northEast : advance soko1_2.board 363 .northEast = none := by decide +kernel
theorem advanceAt363_northWest : advance soko1_2.board 363 .northWest = some 336 := by decide +kernel
theorem advanceAt363_southEast : advance soko1_2.board 363 .southEast = none := by decide +kernel
theorem advanceAt363_southWest : advance soko1_2.board 363 .southWest = some 388 := by decide +kernel
theorem floorAt364 : soko1_2.board.floor.contains 364 = false := by decide +kernel
theorem doorAt364 : soko1_2.board.doors.contains 364 = false := by decide +kernel
theorem trapAt364 : soko1_2.board.rollingTraps.contains 364 = false := by decide +kernel
theorem boxAt364 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 364 = false := rfl
theorem holeAt364 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 364 = false := rfl
theorem advanceAt364_north : advance soko1_2.board 364 .north = some 338 := by decide +kernel
theorem advanceAt364_south : advance soko1_2.board 364 .south = some 390 := by decide +kernel
theorem advanceAt364_east : advance soko1_2.board 364 .east = some 365 := by decide +kernel
theorem advanceAt364_west : advance soko1_2.board 364 .west = none := by decide +kernel
theorem advanceAt364_northEast : advance soko1_2.board 364 .northEast = some 339 := by decide +kernel
theorem advanceAt364_northWest : advance soko1_2.board 364 .northWest = none := by decide +kernel
theorem advanceAt364_southEast : advance soko1_2.board 364 .southEast = some 391 := by decide +kernel
theorem advanceAt364_southWest : advance soko1_2.board 364 .southWest = none := by decide +kernel
theorem floorAt365 : soko1_2.board.floor.contains 365 = false := by decide +kernel
theorem doorAt365 : soko1_2.board.doors.contains 365 = false := by decide +kernel
theorem trapAt365 : soko1_2.board.rollingTraps.contains 365 = false := by decide +kernel
theorem boxAt365 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 365 = false := rfl
theorem holeAt365 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 365 = false := rfl
theorem advanceAt365_north : advance soko1_2.board 365 .north = some 339 := by decide +kernel
theorem advanceAt365_south : advance soko1_2.board 365 .south = some 391 := by decide +kernel
theorem advanceAt365_east : advance soko1_2.board 365 .east = some 366 := by decide +kernel
theorem advanceAt365_west : advance soko1_2.board 365 .west = some 364 := by decide +kernel
theorem advanceAt365_northEast : advance soko1_2.board 365 .northEast = some 340 := by decide +kernel
theorem advanceAt365_northWest : advance soko1_2.board 365 .northWest = some 338 := by decide +kernel
theorem advanceAt365_southEast : advance soko1_2.board 365 .southEast = some 392 := by decide +kernel
theorem advanceAt365_southWest : advance soko1_2.board 365 .southWest = some 390 := by decide +kernel
theorem floorAt366 : soko1_2.board.floor.contains 366 = false := by decide +kernel
theorem doorAt366 : soko1_2.board.doors.contains 366 = false := by decide +kernel
theorem trapAt366 : soko1_2.board.rollingTraps.contains 366 = false := by decide +kernel
theorem boxAt366 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 366 = false := rfl
theorem holeAt366 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 366 = false := rfl
theorem advanceAt366_north : advance soko1_2.board 366 .north = some 340 := by decide +kernel
theorem advanceAt366_south : advance soko1_2.board 366 .south = some 392 := by decide +kernel
theorem advanceAt366_east : advance soko1_2.board 366 .east = some 367 := by decide +kernel
theorem advanceAt366_west : advance soko1_2.board 366 .west = some 365 := by decide +kernel
theorem advanceAt366_northEast : advance soko1_2.board 366 .northEast = some 341 := by decide +kernel
theorem advanceAt366_northWest : advance soko1_2.board 366 .northWest = some 339 := by decide +kernel
theorem advanceAt366_southEast : advance soko1_2.board 366 .southEast = some 393 := by decide +kernel
theorem advanceAt366_southWest : advance soko1_2.board 366 .southWest = some 391 := by decide +kernel
theorem floorAt367 : soko1_2.board.floor.contains 367 = false := by decide +kernel
theorem doorAt367 : soko1_2.board.doors.contains 367 = false := by decide +kernel
theorem trapAt367 : soko1_2.board.rollingTraps.contains 367 = false := by decide +kernel
theorem boxAt367 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 367 = false := rfl
theorem holeAt367 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 367 = false := rfl
theorem advanceAt367_north : advance soko1_2.board 367 .north = some 341 := by decide +kernel
theorem advanceAt367_south : advance soko1_2.board 367 .south = some 393 := by decide +kernel
theorem advanceAt367_east : advance soko1_2.board 367 .east = some 368 := by decide +kernel
theorem advanceAt367_west : advance soko1_2.board 367 .west = some 366 := by decide +kernel
theorem advanceAt367_northEast : advance soko1_2.board 367 .northEast = some 342 := by decide +kernel
theorem advanceAt367_northWest : advance soko1_2.board 367 .northWest = some 340 := by decide +kernel
theorem advanceAt367_southEast : advance soko1_2.board 367 .southEast = some 394 := by decide +kernel
theorem advanceAt367_southWest : advance soko1_2.board 367 .southWest = some 392 := by decide +kernel
theorem floorAt368 : soko1_2.board.floor.contains 368 = false := by decide +kernel
theorem doorAt368 : soko1_2.board.doors.contains 368 = false := by decide +kernel
theorem trapAt368 : soko1_2.board.rollingTraps.contains 368 = false := by decide +kernel
theorem boxAt368 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 368 = false := rfl
theorem holeAt368 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 368 = false := rfl
theorem advanceAt368_north : advance soko1_2.board 368 .north = some 342 := by decide +kernel
theorem advanceAt368_south : advance soko1_2.board 368 .south = some 394 := by decide +kernel
theorem advanceAt368_east : advance soko1_2.board 368 .east = some 369 := by decide +kernel
theorem advanceAt368_west : advance soko1_2.board 368 .west = some 367 := by decide +kernel
theorem advanceAt368_northEast : advance soko1_2.board 368 .northEast = some 343 := by decide +kernel
theorem advanceAt368_northWest : advance soko1_2.board 368 .northWest = some 341 := by decide +kernel
theorem advanceAt368_southEast : advance soko1_2.board 368 .southEast = some 395 := by decide +kernel
theorem advanceAt368_southWest : advance soko1_2.board 368 .southWest = some 393 := by decide +kernel
theorem floorAt369 : soko1_2.board.floor.contains 369 = false := by decide +kernel
theorem doorAt369 : soko1_2.board.doors.contains 369 = false := by decide +kernel
theorem trapAt369 : soko1_2.board.rollingTraps.contains 369 = false := by decide +kernel
theorem boxAt369 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 369 = false := rfl
theorem holeAt369 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 369 = false := rfl
theorem advanceAt369_north : advance soko1_2.board 369 .north = some 343 := by decide +kernel
theorem advanceAt369_south : advance soko1_2.board 369 .south = some 395 := by decide +kernel
theorem advanceAt369_east : advance soko1_2.board 369 .east = some 370 := by decide +kernel
theorem advanceAt369_west : advance soko1_2.board 369 .west = some 368 := by decide +kernel
theorem advanceAt369_northEast : advance soko1_2.board 369 .northEast = some 344 := by decide +kernel
theorem advanceAt369_northWest : advance soko1_2.board 369 .northWest = some 342 := by decide +kernel
theorem advanceAt369_southEast : advance soko1_2.board 369 .southEast = some 396 := by decide +kernel
theorem advanceAt369_southWest : advance soko1_2.board 369 .southWest = some 394 := by decide +kernel
theorem floorAt370 : soko1_2.board.floor.contains 370 = true := by decide +kernel
theorem doorAt370 : soko1_2.board.doors.contains 370 = false := by decide +kernel
theorem trapAt370 : soko1_2.board.rollingTraps.contains 370 = false := by decide +kernel
theorem boxAt370 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 370 = p 370 := rfl
theorem holeAt370 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 370 = false := rfl
theorem advanceAt370_north : advance soko1_2.board 370 .north = some 344 := by decide +kernel
theorem advanceAt370_south : advance soko1_2.board 370 .south = some 396 := by decide +kernel
theorem advanceAt370_east : advance soko1_2.board 370 .east = some 371 := by decide +kernel
theorem advanceAt370_west : advance soko1_2.board 370 .west = some 369 := by decide +kernel
theorem advanceAt370_northEast : advance soko1_2.board 370 .northEast = some 345 := by decide +kernel
theorem advanceAt370_northWest : advance soko1_2.board 370 .northWest = some 343 := by decide +kernel
theorem advanceAt370_southEast : advance soko1_2.board 370 .southEast = some 397 := by decide +kernel
theorem advanceAt370_southWest : advance soko1_2.board 370 .southWest = some 395 := by decide +kernel
theorem floorAt371 : soko1_2.board.floor.contains 371 = true := by decide +kernel
theorem doorAt371 : soko1_2.board.doors.contains 371 = false := by decide +kernel
theorem trapAt371 : soko1_2.board.rollingTraps.contains 371 = false := by decide +kernel
theorem boxAt371 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 371 = p 371 := rfl
theorem holeAt371 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 371 = false := rfl
theorem advanceAt371_north : advance soko1_2.board 371 .north = some 345 := by decide +kernel
theorem advanceAt371_south : advance soko1_2.board 371 .south = some 397 := by decide +kernel
theorem advanceAt371_east : advance soko1_2.board 371 .east = some 372 := by decide +kernel
theorem advanceAt371_west : advance soko1_2.board 371 .west = some 370 := by decide +kernel
theorem advanceAt371_northEast : advance soko1_2.board 371 .northEast = some 346 := by decide +kernel
theorem advanceAt371_northWest : advance soko1_2.board 371 .northWest = some 344 := by decide +kernel
theorem advanceAt371_southEast : advance soko1_2.board 371 .southEast = some 398 := by decide +kernel
theorem advanceAt371_southWest : advance soko1_2.board 371 .southWest = some 396 := by decide +kernel
theorem floorAt372 : soko1_2.board.floor.contains 372 = true := by decide +kernel
theorem doorAt372 : soko1_2.board.doors.contains 372 = false := by decide +kernel
theorem trapAt372 : soko1_2.board.rollingTraps.contains 372 = false := by decide +kernel
theorem boxAt372 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 372 = p 372 := rfl
theorem holeAt372 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 372 = false := rfl
theorem advanceAt372_north : advance soko1_2.board 372 .north = some 346 := by decide +kernel
theorem advanceAt372_south : advance soko1_2.board 372 .south = some 398 := by decide +kernel
theorem advanceAt372_east : advance soko1_2.board 372 .east = some 373 := by decide +kernel
theorem advanceAt372_west : advance soko1_2.board 372 .west = some 371 := by decide +kernel
theorem advanceAt372_northEast : advance soko1_2.board 372 .northEast = some 347 := by decide +kernel
theorem advanceAt372_northWest : advance soko1_2.board 372 .northWest = some 345 := by decide +kernel
theorem advanceAt372_southEast : advance soko1_2.board 372 .southEast = some 399 := by decide +kernel
theorem advanceAt372_southWest : advance soko1_2.board 372 .southWest = some 397 := by decide +kernel
theorem floorAt373 : soko1_2.board.floor.contains 373 = true := by decide +kernel
theorem doorAt373 : soko1_2.board.doors.contains 373 = false := by decide +kernel
theorem trapAt373 : soko1_2.board.rollingTraps.contains 373 = false := by decide +kernel
theorem boxAt373 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 373 = p 373 := rfl
theorem holeAt373 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 373 = false := rfl
theorem advanceAt373_north : advance soko1_2.board 373 .north = some 347 := by decide +kernel
theorem advanceAt373_south : advance soko1_2.board 373 .south = some 399 := by decide +kernel
theorem advanceAt373_east : advance soko1_2.board 373 .east = some 374 := by decide +kernel
theorem advanceAt373_west : advance soko1_2.board 373 .west = some 372 := by decide +kernel
theorem advanceAt373_northEast : advance soko1_2.board 373 .northEast = some 348 := by decide +kernel
theorem advanceAt373_northWest : advance soko1_2.board 373 .northWest = some 346 := by decide +kernel
theorem advanceAt373_southEast : advance soko1_2.board 373 .southEast = some 400 := by decide +kernel
theorem advanceAt373_southWest : advance soko1_2.board 373 .southWest = some 398 := by decide +kernel
theorem floorAt374 : soko1_2.board.floor.contains 374 = true := by decide +kernel
theorem doorAt374 : soko1_2.board.doors.contains 374 = false := by decide +kernel
theorem trapAt374 : soko1_2.board.rollingTraps.contains 374 = false := by decide +kernel
theorem boxAt374 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 374 = p 374 := rfl
theorem holeAt374 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 374 = false := rfl
theorem advanceAt374_north : advance soko1_2.board 374 .north = some 348 := by decide +kernel
theorem advanceAt374_south : advance soko1_2.board 374 .south = some 400 := by decide +kernel
theorem advanceAt374_east : advance soko1_2.board 374 .east = some 375 := by decide +kernel
theorem advanceAt374_west : advance soko1_2.board 374 .west = some 373 := by decide +kernel
theorem advanceAt374_northEast : advance soko1_2.board 374 .northEast = some 349 := by decide +kernel
theorem advanceAt374_northWest : advance soko1_2.board 374 .northWest = some 347 := by decide +kernel
theorem advanceAt374_southEast : advance soko1_2.board 374 .southEast = some 401 := by decide +kernel
theorem advanceAt374_southWest : advance soko1_2.board 374 .southWest = some 399 := by decide +kernel
theorem floorAt375 : soko1_2.board.floor.contains 375 = false := by decide +kernel
theorem doorAt375 : soko1_2.board.doors.contains 375 = false := by decide +kernel
theorem trapAt375 : soko1_2.board.rollingTraps.contains 375 = false := by decide +kernel
theorem boxAt375 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 375 = false := rfl
theorem holeAt375 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 375 = false := rfl
theorem advanceAt375_north : advance soko1_2.board 375 .north = some 349 := by decide +kernel
theorem advanceAt375_south : advance soko1_2.board 375 .south = some 401 := by decide +kernel
theorem advanceAt375_east : advance soko1_2.board 375 .east = some 376 := by decide +kernel
theorem advanceAt375_west : advance soko1_2.board 375 .west = some 374 := by decide +kernel
theorem advanceAt375_northEast : advance soko1_2.board 375 .northEast = some 350 := by decide +kernel
theorem advanceAt375_northWest : advance soko1_2.board 375 .northWest = some 348 := by decide +kernel
theorem advanceAt375_southEast : advance soko1_2.board 375 .southEast = some 402 := by decide +kernel
theorem advanceAt375_southWest : advance soko1_2.board 375 .southWest = some 400 := by decide +kernel
theorem floorAt376 : soko1_2.board.floor.contains 376 = false := by decide +kernel
theorem doorAt376 : soko1_2.board.doors.contains 376 = false := by decide +kernel
theorem trapAt376 : soko1_2.board.rollingTraps.contains 376 = false := by decide +kernel
theorem boxAt376 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 376 = false := rfl
theorem holeAt376 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 376 = false := rfl
theorem advanceAt376_north : advance soko1_2.board 376 .north = some 350 := by decide +kernel
theorem advanceAt376_south : advance soko1_2.board 376 .south = some 402 := by decide +kernel
theorem advanceAt376_east : advance soko1_2.board 376 .east = some 377 := by decide +kernel
theorem advanceAt376_west : advance soko1_2.board 376 .west = some 375 := by decide +kernel
theorem advanceAt376_northEast : advance soko1_2.board 376 .northEast = some 351 := by decide +kernel
theorem advanceAt376_northWest : advance soko1_2.board 376 .northWest = some 349 := by decide +kernel
theorem advanceAt376_southEast : advance soko1_2.board 376 .southEast = some 403 := by decide +kernel
theorem advanceAt376_southWest : advance soko1_2.board 376 .southWest = some 401 := by decide +kernel
theorem floorAt377 : soko1_2.board.floor.contains 377 = false := by decide +kernel
theorem doorAt377 : soko1_2.board.doors.contains 377 = false := by decide +kernel
theorem trapAt377 : soko1_2.board.rollingTraps.contains 377 = false := by decide +kernel
theorem boxAt377 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 377 = false := rfl
theorem holeAt377 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 377 = false := rfl
theorem advanceAt377_north : advance soko1_2.board 377 .north = some 351 := by decide +kernel
theorem advanceAt377_south : advance soko1_2.board 377 .south = some 403 := by decide +kernel
theorem advanceAt377_east : advance soko1_2.board 377 .east = some 378 := by decide +kernel
theorem advanceAt377_west : advance soko1_2.board 377 .west = some 376 := by decide +kernel
theorem advanceAt377_northEast : advance soko1_2.board 377 .northEast = some 352 := by decide +kernel
theorem advanceAt377_northWest : advance soko1_2.board 377 .northWest = some 350 := by decide +kernel
theorem advanceAt377_southEast : advance soko1_2.board 377 .southEast = some 404 := by decide +kernel
theorem advanceAt377_southWest : advance soko1_2.board 377 .southWest = some 402 := by decide +kernel
theorem floorAt378 : soko1_2.board.floor.contains 378 = false := by decide +kernel
theorem doorAt378 : soko1_2.board.doors.contains 378 = false := by decide +kernel
theorem trapAt378 : soko1_2.board.rollingTraps.contains 378 = false := by decide +kernel
theorem boxAt378 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 378 = false := rfl
theorem holeAt378 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 378 = false := rfl
theorem advanceAt378_north : advance soko1_2.board 378 .north = some 352 := by decide +kernel
theorem advanceAt378_south : advance soko1_2.board 378 .south = some 404 := by decide +kernel
theorem advanceAt378_east : advance soko1_2.board 378 .east = some 379 := by decide +kernel
theorem advanceAt378_west : advance soko1_2.board 378 .west = some 377 := by decide +kernel
theorem advanceAt378_northEast : advance soko1_2.board 378 .northEast = some 353 := by decide +kernel
theorem advanceAt378_northWest : advance soko1_2.board 378 .northWest = some 351 := by decide +kernel
theorem advanceAt378_southEast : advance soko1_2.board 378 .southEast = some 405 := by decide +kernel
theorem advanceAt378_southWest : advance soko1_2.board 378 .southWest = some 403 := by decide +kernel
theorem floorAt379 : soko1_2.board.floor.contains 379 = false := by decide +kernel
theorem doorAt379 : soko1_2.board.doors.contains 379 = false := by decide +kernel
theorem trapAt379 : soko1_2.board.rollingTraps.contains 379 = false := by decide +kernel
theorem boxAt379 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 379 = false := rfl
theorem holeAt379 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 379 = false := rfl
theorem advanceAt379_north : advance soko1_2.board 379 .north = some 353 := by decide +kernel
theorem advanceAt379_south : advance soko1_2.board 379 .south = some 405 := by decide +kernel
theorem advanceAt379_east : advance soko1_2.board 379 .east = some 380 := by decide +kernel
theorem advanceAt379_west : advance soko1_2.board 379 .west = some 378 := by decide +kernel
theorem advanceAt379_northEast : advance soko1_2.board 379 .northEast = some 354 := by decide +kernel
theorem advanceAt379_northWest : advance soko1_2.board 379 .northWest = some 352 := by decide +kernel
theorem advanceAt379_southEast : advance soko1_2.board 379 .southEast = some 406 := by decide +kernel
theorem advanceAt379_southWest : advance soko1_2.board 379 .southWest = some 404 := by decide +kernel
theorem floorAt380 : soko1_2.board.floor.contains 380 = true := by decide +kernel
theorem doorAt380 : soko1_2.board.doors.contains 380 = false := by decide +kernel
theorem trapAt380 : soko1_2.board.rollingTraps.contains 380 = false := by decide +kernel
theorem boxAt380 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 380 = false := rfl
theorem holeAt380 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 380 = false := rfl
theorem advanceAt380_north : advance soko1_2.board 380 .north = some 354 := by decide +kernel
theorem advanceAt380_south : advance soko1_2.board 380 .south = some 406 := by decide +kernel
theorem advanceAt380_east : advance soko1_2.board 380 .east = some 381 := by decide +kernel
theorem advanceAt380_west : advance soko1_2.board 380 .west = some 379 := by decide +kernel
theorem advanceAt380_northEast : advance soko1_2.board 380 .northEast = some 355 := by decide +kernel
theorem advanceAt380_northWest : advance soko1_2.board 380 .northWest = some 353 := by decide +kernel
theorem advanceAt380_southEast : advance soko1_2.board 380 .southEast = some 407 := by decide +kernel
theorem advanceAt380_southWest : advance soko1_2.board 380 .southWest = some 405 := by decide +kernel
theorem floorAt381 : soko1_2.board.floor.contains 381 = false := by decide +kernel
theorem doorAt381 : soko1_2.board.doors.contains 381 = true := by decide +kernel
theorem trapAt381 : soko1_2.board.rollingTraps.contains 381 = false := by decide +kernel
theorem boxAt381 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 381 = false := rfl
theorem holeAt381 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 381 = false := rfl
theorem advanceAt381_north : advance soko1_2.board 381 .north = some 355 := by decide +kernel
theorem advanceAt381_south : advance soko1_2.board 381 .south = some 407 := by decide +kernel
theorem advanceAt381_east : advance soko1_2.board 381 .east = some 382 := by decide +kernel
theorem advanceAt381_west : advance soko1_2.board 381 .west = some 380 := by decide +kernel
theorem advanceAt381_northEast : advance soko1_2.board 381 .northEast = some 356 := by decide +kernel
theorem advanceAt381_northWest : advance soko1_2.board 381 .northWest = some 354 := by decide +kernel
theorem advanceAt381_southEast : advance soko1_2.board 381 .southEast = some 408 := by decide +kernel
theorem advanceAt381_southWest : advance soko1_2.board 381 .southWest = some 406 := by decide +kernel
theorem floorAt382 : soko1_2.board.floor.contains 382 = true := by decide +kernel
theorem doorAt382 : soko1_2.board.doors.contains 382 = false := by decide +kernel
theorem trapAt382 : soko1_2.board.rollingTraps.contains 382 = false := by decide +kernel
theorem boxAt382 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 382 = false := rfl
theorem holeAt382 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 382 = false := rfl
theorem advanceAt382_north : advance soko1_2.board 382 .north = some 356 := by decide +kernel
theorem advanceAt382_south : advance soko1_2.board 382 .south = some 408 := by decide +kernel
theorem advanceAt382_east : advance soko1_2.board 382 .east = some 383 := by decide +kernel
theorem advanceAt382_west : advance soko1_2.board 382 .west = some 381 := by decide +kernel
theorem advanceAt382_northEast : advance soko1_2.board 382 .northEast = some 357 := by decide +kernel
theorem advanceAt382_northWest : advance soko1_2.board 382 .northWest = some 355 := by decide +kernel
theorem advanceAt382_southEast : advance soko1_2.board 382 .southEast = some 409 := by decide +kernel
theorem advanceAt382_southWest : advance soko1_2.board 382 .southWest = some 407 := by decide +kernel
theorem floorAt383 : soko1_2.board.floor.contains 383 = true := by decide +kernel
theorem doorAt383 : soko1_2.board.doors.contains 383 = false := by decide +kernel
theorem trapAt383 : soko1_2.board.rollingTraps.contains 383 = false := by decide +kernel
theorem boxAt383 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 383 = false := rfl
theorem holeAt383 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 383 = false := rfl
theorem advanceAt383_north : advance soko1_2.board 383 .north = some 357 := by decide +kernel
theorem advanceAt383_south : advance soko1_2.board 383 .south = some 409 := by decide +kernel
theorem advanceAt383_east : advance soko1_2.board 383 .east = some 384 := by decide +kernel
theorem advanceAt383_west : advance soko1_2.board 383 .west = some 382 := by decide +kernel
theorem advanceAt383_northEast : advance soko1_2.board 383 .northEast = some 358 := by decide +kernel
theorem advanceAt383_northWest : advance soko1_2.board 383 .northWest = some 356 := by decide +kernel
theorem advanceAt383_southEast : advance soko1_2.board 383 .southEast = some 410 := by decide +kernel
theorem advanceAt383_southWest : advance soko1_2.board 383 .southWest = some 408 := by decide +kernel
theorem floorAt384 : soko1_2.board.floor.contains 384 = true := by decide +kernel
theorem doorAt384 : soko1_2.board.doors.contains 384 = false := by decide +kernel
theorem trapAt384 : soko1_2.board.rollingTraps.contains 384 = false := by decide +kernel
theorem boxAt384 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 384 = false := rfl
theorem holeAt384 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 384 = false := rfl
theorem advanceAt384_north : advance soko1_2.board 384 .north = some 358 := by decide +kernel
theorem advanceAt384_south : advance soko1_2.board 384 .south = some 410 := by decide +kernel
theorem advanceAt384_east : advance soko1_2.board 384 .east = some 385 := by decide +kernel
theorem advanceAt384_west : advance soko1_2.board 384 .west = some 383 := by decide +kernel
theorem advanceAt384_northEast : advance soko1_2.board 384 .northEast = some 359 := by decide +kernel
theorem advanceAt384_northWest : advance soko1_2.board 384 .northWest = some 357 := by decide +kernel
theorem advanceAt384_southEast : advance soko1_2.board 384 .southEast = some 411 := by decide +kernel
theorem advanceAt384_southWest : advance soko1_2.board 384 .southWest = some 409 := by decide +kernel
theorem floorAt385 : soko1_2.board.floor.contains 385 = true := by decide +kernel
theorem doorAt385 : soko1_2.board.doors.contains 385 = false := by decide +kernel
theorem trapAt385 : soko1_2.board.rollingTraps.contains 385 = false := by decide +kernel
theorem boxAt385 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 385 = false := rfl
theorem holeAt385 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 385 = false := rfl
theorem advanceAt385_north : advance soko1_2.board 385 .north = some 359 := by decide +kernel
theorem advanceAt385_south : advance soko1_2.board 385 .south = some 411 := by decide +kernel
theorem advanceAt385_east : advance soko1_2.board 385 .east = some 386 := by decide +kernel
theorem advanceAt385_west : advance soko1_2.board 385 .west = some 384 := by decide +kernel
theorem advanceAt385_northEast : advance soko1_2.board 385 .northEast = some 360 := by decide +kernel
theorem advanceAt385_northWest : advance soko1_2.board 385 .northWest = some 358 := by decide +kernel
theorem advanceAt385_southEast : advance soko1_2.board 385 .southEast = some 412 := by decide +kernel
theorem advanceAt385_southWest : advance soko1_2.board 385 .southWest = some 410 := by decide +kernel
theorem floorAt386 : soko1_2.board.floor.contains 386 = true := by decide +kernel
theorem doorAt386 : soko1_2.board.doors.contains 386 = false := by decide +kernel
theorem trapAt386 : soko1_2.board.rollingTraps.contains 386 = false := by decide +kernel
theorem boxAt386 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 386 = false := rfl
theorem holeAt386 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 386 = false := rfl
theorem advanceAt386_north : advance soko1_2.board 386 .north = some 360 := by decide +kernel
theorem advanceAt386_south : advance soko1_2.board 386 .south = some 412 := by decide +kernel
theorem advanceAt386_east : advance soko1_2.board 386 .east = some 387 := by decide +kernel
theorem advanceAt386_west : advance soko1_2.board 386 .west = some 385 := by decide +kernel
theorem advanceAt386_northEast : advance soko1_2.board 386 .northEast = some 361 := by decide +kernel
theorem advanceAt386_northWest : advance soko1_2.board 386 .northWest = some 359 := by decide +kernel
theorem advanceAt386_southEast : advance soko1_2.board 386 .southEast = some 413 := by decide +kernel
theorem advanceAt386_southWest : advance soko1_2.board 386 .southWest = some 411 := by decide +kernel
theorem floorAt387 : soko1_2.board.floor.contains 387 = false := by decide +kernel
theorem doorAt387 : soko1_2.board.doors.contains 387 = false := by decide +kernel
theorem trapAt387 : soko1_2.board.rollingTraps.contains 387 = false := by decide +kernel
theorem boxAt387 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 387 = false := rfl
theorem holeAt387 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 387 = false := rfl
theorem advanceAt387_north : advance soko1_2.board 387 .north = some 361 := by decide +kernel
theorem advanceAt387_south : advance soko1_2.board 387 .south = some 413 := by decide +kernel
theorem advanceAt387_east : advance soko1_2.board 387 .east = some 388 := by decide +kernel
theorem advanceAt387_west : advance soko1_2.board 387 .west = some 386 := by decide +kernel
theorem advanceAt387_northEast : advance soko1_2.board 387 .northEast = some 362 := by decide +kernel
theorem advanceAt387_northWest : advance soko1_2.board 387 .northWest = some 360 := by decide +kernel
theorem advanceAt387_southEast : advance soko1_2.board 387 .southEast = some 414 := by decide +kernel
theorem advanceAt387_southWest : advance soko1_2.board 387 .southWest = some 412 := by decide +kernel
theorem floorAt388 : soko1_2.board.floor.contains 388 = false := by decide +kernel
theorem doorAt388 : soko1_2.board.doors.contains 388 = false := by decide +kernel
theorem trapAt388 : soko1_2.board.rollingTraps.contains 388 = false := by decide +kernel
theorem boxAt388 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 388 = false := rfl
theorem holeAt388 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 388 = false := rfl
theorem advanceAt388_north : advance soko1_2.board 388 .north = some 362 := by decide +kernel
theorem advanceAt388_south : advance soko1_2.board 388 .south = some 414 := by decide +kernel
theorem advanceAt388_east : advance soko1_2.board 388 .east = some 389 := by decide +kernel
theorem advanceAt388_west : advance soko1_2.board 388 .west = some 387 := by decide +kernel
theorem advanceAt388_northEast : advance soko1_2.board 388 .northEast = some 363 := by decide +kernel
theorem advanceAt388_northWest : advance soko1_2.board 388 .northWest = some 361 := by decide +kernel
theorem advanceAt388_southEast : advance soko1_2.board 388 .southEast = some 415 := by decide +kernel
theorem advanceAt388_southWest : advance soko1_2.board 388 .southWest = some 413 := by decide +kernel
theorem floorAt389 : soko1_2.board.floor.contains 389 = false := by decide +kernel
theorem doorAt389 : soko1_2.board.doors.contains 389 = false := by decide +kernel
theorem trapAt389 : soko1_2.board.rollingTraps.contains 389 = false := by decide +kernel
theorem boxAt389 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 389 = false := rfl
theorem holeAt389 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 389 = false := rfl
theorem advanceAt389_north : advance soko1_2.board 389 .north = some 363 := by decide +kernel
theorem advanceAt389_south : advance soko1_2.board 389 .south = some 415 := by decide +kernel
theorem advanceAt389_east : advance soko1_2.board 389 .east = none := by decide +kernel
theorem advanceAt389_west : advance soko1_2.board 389 .west = some 388 := by decide +kernel
theorem advanceAt389_northEast : advance soko1_2.board 389 .northEast = none := by decide +kernel
theorem advanceAt389_northWest : advance soko1_2.board 389 .northWest = some 362 := by decide +kernel
theorem advanceAt389_southEast : advance soko1_2.board 389 .southEast = none := by decide +kernel
theorem advanceAt389_southWest : advance soko1_2.board 389 .southWest = some 414 := by decide +kernel
theorem floorAt390 : soko1_2.board.floor.contains 390 = false := by decide +kernel
theorem doorAt390 : soko1_2.board.doors.contains 390 = false := by decide +kernel
theorem trapAt390 : soko1_2.board.rollingTraps.contains 390 = false := by decide +kernel
theorem boxAt390 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 390 = false := rfl
theorem holeAt390 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 390 = false := rfl
theorem advanceAt390_north : advance soko1_2.board 390 .north = some 364 := by decide +kernel
theorem advanceAt390_south : advance soko1_2.board 390 .south = some 416 := by decide +kernel
theorem advanceAt390_east : advance soko1_2.board 390 .east = some 391 := by decide +kernel
theorem advanceAt390_west : advance soko1_2.board 390 .west = none := by decide +kernel
theorem advanceAt390_northEast : advance soko1_2.board 390 .northEast = some 365 := by decide +kernel
theorem advanceAt390_northWest : advance soko1_2.board 390 .northWest = none := by decide +kernel
theorem advanceAt390_southEast : advance soko1_2.board 390 .southEast = some 417 := by decide +kernel
theorem advanceAt390_southWest : advance soko1_2.board 390 .southWest = none := by decide +kernel
theorem floorAt391 : soko1_2.board.floor.contains 391 = false := by decide +kernel
theorem doorAt391 : soko1_2.board.doors.contains 391 = false := by decide +kernel
theorem trapAt391 : soko1_2.board.rollingTraps.contains 391 = false := by decide +kernel
theorem boxAt391 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 391 = false := rfl
theorem holeAt391 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 391 = false := rfl
theorem advanceAt391_north : advance soko1_2.board 391 .north = some 365 := by decide +kernel
theorem advanceAt391_south : advance soko1_2.board 391 .south = some 417 := by decide +kernel
theorem advanceAt391_east : advance soko1_2.board 391 .east = some 392 := by decide +kernel
theorem advanceAt391_west : advance soko1_2.board 391 .west = some 390 := by decide +kernel
theorem advanceAt391_northEast : advance soko1_2.board 391 .northEast = some 366 := by decide +kernel
theorem advanceAt391_northWest : advance soko1_2.board 391 .northWest = some 364 := by decide +kernel
theorem advanceAt391_southEast : advance soko1_2.board 391 .southEast = some 418 := by decide +kernel
theorem advanceAt391_southWest : advance soko1_2.board 391 .southWest = some 416 := by decide +kernel
theorem floorAt392 : soko1_2.board.floor.contains 392 = false := by decide +kernel
theorem doorAt392 : soko1_2.board.doors.contains 392 = false := by decide +kernel
theorem trapAt392 : soko1_2.board.rollingTraps.contains 392 = false := by decide +kernel
theorem boxAt392 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 392 = false := rfl
theorem holeAt392 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 392 = false := rfl
theorem advanceAt392_north : advance soko1_2.board 392 .north = some 366 := by decide +kernel
theorem advanceAt392_south : advance soko1_2.board 392 .south = some 418 := by decide +kernel
theorem advanceAt392_east : advance soko1_2.board 392 .east = some 393 := by decide +kernel
theorem advanceAt392_west : advance soko1_2.board 392 .west = some 391 := by decide +kernel
theorem advanceAt392_northEast : advance soko1_2.board 392 .northEast = some 367 := by decide +kernel
theorem advanceAt392_northWest : advance soko1_2.board 392 .northWest = some 365 := by decide +kernel
theorem advanceAt392_southEast : advance soko1_2.board 392 .southEast = some 419 := by decide +kernel
theorem advanceAt392_southWest : advance soko1_2.board 392 .southWest = some 417 := by decide +kernel
theorem floorAt393 : soko1_2.board.floor.contains 393 = false := by decide +kernel
theorem doorAt393 : soko1_2.board.doors.contains 393 = false := by decide +kernel
theorem trapAt393 : soko1_2.board.rollingTraps.contains 393 = false := by decide +kernel
theorem boxAt393 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 393 = false := rfl
theorem holeAt393 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 393 = false := rfl
theorem advanceAt393_north : advance soko1_2.board 393 .north = some 367 := by decide +kernel
theorem advanceAt393_south : advance soko1_2.board 393 .south = some 419 := by decide +kernel
theorem advanceAt393_east : advance soko1_2.board 393 .east = some 394 := by decide +kernel
theorem advanceAt393_west : advance soko1_2.board 393 .west = some 392 := by decide +kernel
theorem advanceAt393_northEast : advance soko1_2.board 393 .northEast = some 368 := by decide +kernel
theorem advanceAt393_northWest : advance soko1_2.board 393 .northWest = some 366 := by decide +kernel
theorem advanceAt393_southEast : advance soko1_2.board 393 .southEast = some 420 := by decide +kernel
theorem advanceAt393_southWest : advance soko1_2.board 393 .southWest = some 418 := by decide +kernel
theorem floorAt394 : soko1_2.board.floor.contains 394 = false := by decide +kernel
theorem doorAt394 : soko1_2.board.doors.contains 394 = false := by decide +kernel
theorem trapAt394 : soko1_2.board.rollingTraps.contains 394 = false := by decide +kernel
theorem boxAt394 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 394 = false := rfl
theorem holeAt394 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 394 = false := rfl
theorem advanceAt394_north : advance soko1_2.board 394 .north = some 368 := by decide +kernel
theorem advanceAt394_south : advance soko1_2.board 394 .south = some 420 := by decide +kernel
theorem advanceAt394_east : advance soko1_2.board 394 .east = some 395 := by decide +kernel
theorem advanceAt394_west : advance soko1_2.board 394 .west = some 393 := by decide +kernel
theorem advanceAt394_northEast : advance soko1_2.board 394 .northEast = some 369 := by decide +kernel
theorem advanceAt394_northWest : advance soko1_2.board 394 .northWest = some 367 := by decide +kernel
theorem advanceAt394_southEast : advance soko1_2.board 394 .southEast = some 421 := by decide +kernel
theorem advanceAt394_southWest : advance soko1_2.board 394 .southWest = some 419 := by decide +kernel
theorem floorAt395 : soko1_2.board.floor.contains 395 = false := by decide +kernel
theorem doorAt395 : soko1_2.board.doors.contains 395 = false := by decide +kernel
theorem trapAt395 : soko1_2.board.rollingTraps.contains 395 = false := by decide +kernel
theorem boxAt395 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 395 = false := rfl
theorem holeAt395 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 395 = false := rfl
theorem advanceAt395_north : advance soko1_2.board 395 .north = some 369 := by decide +kernel
theorem advanceAt395_south : advance soko1_2.board 395 .south = some 421 := by decide +kernel
theorem advanceAt395_east : advance soko1_2.board 395 .east = some 396 := by decide +kernel
theorem advanceAt395_west : advance soko1_2.board 395 .west = some 394 := by decide +kernel
theorem advanceAt395_northEast : advance soko1_2.board 395 .northEast = some 370 := by decide +kernel
theorem advanceAt395_northWest : advance soko1_2.board 395 .northWest = some 368 := by decide +kernel
theorem advanceAt395_southEast : advance soko1_2.board 395 .southEast = some 422 := by decide +kernel
theorem advanceAt395_southWest : advance soko1_2.board 395 .southWest = some 420 := by decide +kernel
theorem floorAt396 : soko1_2.board.floor.contains 396 = true := by decide +kernel
theorem doorAt396 : soko1_2.board.doors.contains 396 = false := by decide +kernel
theorem trapAt396 : soko1_2.board.rollingTraps.contains 396 = false := by decide +kernel
theorem boxAt396 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 396 = false := rfl
theorem holeAt396 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 396 = false := rfl
theorem advanceAt396_north : advance soko1_2.board 396 .north = some 370 := by decide +kernel
theorem advanceAt396_south : advance soko1_2.board 396 .south = some 422 := by decide +kernel
theorem advanceAt396_east : advance soko1_2.board 396 .east = some 397 := by decide +kernel
theorem advanceAt396_west : advance soko1_2.board 396 .west = some 395 := by decide +kernel
theorem advanceAt396_northEast : advance soko1_2.board 396 .northEast = some 371 := by decide +kernel
theorem advanceAt396_northWest : advance soko1_2.board 396 .northWest = some 369 := by decide +kernel
theorem advanceAt396_southEast : advance soko1_2.board 396 .southEast = some 423 := by decide +kernel
theorem advanceAt396_southWest : advance soko1_2.board 396 .southWest = some 421 := by decide +kernel
theorem floorAt397 : soko1_2.board.floor.contains 397 = true := by decide +kernel
theorem doorAt397 : soko1_2.board.doors.contains 397 = false := by decide +kernel
theorem trapAt397 : soko1_2.board.rollingTraps.contains 397 = false := by decide +kernel
theorem boxAt397 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 397 = p 397 := rfl
theorem holeAt397 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 397 = false := rfl
theorem advanceAt397_north : advance soko1_2.board 397 .north = some 371 := by decide +kernel
theorem advanceAt397_south : advance soko1_2.board 397 .south = some 423 := by decide +kernel
theorem advanceAt397_east : advance soko1_2.board 397 .east = some 398 := by decide +kernel
theorem advanceAt397_west : advance soko1_2.board 397 .west = some 396 := by decide +kernel
theorem advanceAt397_northEast : advance soko1_2.board 397 .northEast = some 372 := by decide +kernel
theorem advanceAt397_northWest : advance soko1_2.board 397 .northWest = some 370 := by decide +kernel
theorem advanceAt397_southEast : advance soko1_2.board 397 .southEast = some 424 := by decide +kernel
theorem advanceAt397_southWest : advance soko1_2.board 397 .southWest = some 422 := by decide +kernel
theorem floorAt398 : soko1_2.board.floor.contains 398 = false := by decide +kernel
theorem doorAt398 : soko1_2.board.doors.contains 398 = false := by decide +kernel
theorem trapAt398 : soko1_2.board.rollingTraps.contains 398 = false := by decide +kernel
theorem boxAt398 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 398 = false := rfl
theorem holeAt398 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 398 = false := rfl
theorem advanceAt398_north : advance soko1_2.board 398 .north = some 372 := by decide +kernel
theorem advanceAt398_south : advance soko1_2.board 398 .south = some 424 := by decide +kernel
theorem advanceAt398_east : advance soko1_2.board 398 .east = some 399 := by decide +kernel
theorem advanceAt398_west : advance soko1_2.board 398 .west = some 397 := by decide +kernel
theorem advanceAt398_northEast : advance soko1_2.board 398 .northEast = some 373 := by decide +kernel
theorem advanceAt398_northWest : advance soko1_2.board 398 .northWest = some 371 := by decide +kernel
theorem advanceAt398_southEast : advance soko1_2.board 398 .southEast = some 425 := by decide +kernel
theorem advanceAt398_southWest : advance soko1_2.board 398 .southWest = some 423 := by decide +kernel
theorem floorAt399 : soko1_2.board.floor.contains 399 = true := by decide +kernel
theorem doorAt399 : soko1_2.board.doors.contains 399 = false := by decide +kernel
theorem trapAt399 : soko1_2.board.rollingTraps.contains 399 = false := by decide +kernel
theorem boxAt399 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 399 = false := rfl
theorem holeAt399 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 399 = false := rfl
theorem advanceAt399_north : advance soko1_2.board 399 .north = some 373 := by decide +kernel
theorem advanceAt399_south : advance soko1_2.board 399 .south = some 425 := by decide +kernel
theorem advanceAt399_east : advance soko1_2.board 399 .east = some 400 := by decide +kernel
theorem advanceAt399_west : advance soko1_2.board 399 .west = some 398 := by decide +kernel
theorem advanceAt399_northEast : advance soko1_2.board 399 .northEast = some 374 := by decide +kernel
theorem advanceAt399_northWest : advance soko1_2.board 399 .northWest = some 372 := by decide +kernel
theorem advanceAt399_southEast : advance soko1_2.board 399 .southEast = some 426 := by decide +kernel
theorem advanceAt399_southWest : advance soko1_2.board 399 .southWest = some 424 := by decide +kernel
end NetHack.Soko12Forward220.Unified.P03
