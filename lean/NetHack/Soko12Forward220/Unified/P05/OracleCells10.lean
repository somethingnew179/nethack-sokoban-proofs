import NetHack.Soko12Forward220.Unified.P05.OracleCells09
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P05
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem floorAt400 : soko1_2.board.floor.contains 400 = true := by decide +kernel
theorem doorAt400 : soko1_2.board.doors.contains 400 = false := by decide +kernel
theorem trapAt400 : soko1_2.board.rollingTraps.contains 400 = false := by decide +kernel
theorem boxAt400 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 400 = p 400 := rfl
theorem holeAt400 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 400 = false := rfl
theorem advanceAt400_north : advance soko1_2.board 400 .north = some 374 := by decide +kernel
theorem advanceAt400_south : advance soko1_2.board 400 .south = some 426 := by decide +kernel
theorem advanceAt400_east : advance soko1_2.board 400 .east = some 401 := by decide +kernel
theorem advanceAt400_west : advance soko1_2.board 400 .west = some 399 := by decide +kernel
theorem advanceAt400_northEast : advance soko1_2.board 400 .northEast = some 375 := by decide +kernel
theorem advanceAt400_northWest : advance soko1_2.board 400 .northWest = some 373 := by decide +kernel
theorem advanceAt400_southEast : advance soko1_2.board 400 .southEast = some 427 := by decide +kernel
theorem advanceAt400_southWest : advance soko1_2.board 400 .southWest = some 425 := by decide +kernel
theorem floorAt401 : soko1_2.board.floor.contains 401 = false := by decide +kernel
theorem doorAt401 : soko1_2.board.doors.contains 401 = false := by decide +kernel
theorem trapAt401 : soko1_2.board.rollingTraps.contains 401 = false := by decide +kernel
theorem boxAt401 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 401 = false := rfl
theorem holeAt401 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 401 = false := rfl
theorem advanceAt401_north : advance soko1_2.board 401 .north = some 375 := by decide +kernel
theorem advanceAt401_south : advance soko1_2.board 401 .south = some 427 := by decide +kernel
theorem advanceAt401_east : advance soko1_2.board 401 .east = some 402 := by decide +kernel
theorem advanceAt401_west : advance soko1_2.board 401 .west = some 400 := by decide +kernel
theorem advanceAt401_northEast : advance soko1_2.board 401 .northEast = some 376 := by decide +kernel
theorem advanceAt401_northWest : advance soko1_2.board 401 .northWest = some 374 := by decide +kernel
theorem advanceAt401_southEast : advance soko1_2.board 401 .southEast = some 428 := by decide +kernel
theorem advanceAt401_southWest : advance soko1_2.board 401 .southWest = some 426 := by decide +kernel
theorem floorAt402 : soko1_2.board.floor.contains 402 = false := by decide +kernel
theorem doorAt402 : soko1_2.board.doors.contains 402 = false := by decide +kernel
theorem trapAt402 : soko1_2.board.rollingTraps.contains 402 = false := by decide +kernel
theorem boxAt402 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 402 = false := rfl
theorem holeAt402 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 402 = false := rfl
theorem advanceAt402_north : advance soko1_2.board 402 .north = some 376 := by decide +kernel
theorem advanceAt402_south : advance soko1_2.board 402 .south = some 428 := by decide +kernel
theorem advanceAt402_east : advance soko1_2.board 402 .east = some 403 := by decide +kernel
theorem advanceAt402_west : advance soko1_2.board 402 .west = some 401 := by decide +kernel
theorem advanceAt402_northEast : advance soko1_2.board 402 .northEast = some 377 := by decide +kernel
theorem advanceAt402_northWest : advance soko1_2.board 402 .northWest = some 375 := by decide +kernel
theorem advanceAt402_southEast : advance soko1_2.board 402 .southEast = some 429 := by decide +kernel
theorem advanceAt402_southWest : advance soko1_2.board 402 .southWest = some 427 := by decide +kernel
theorem floorAt403 : soko1_2.board.floor.contains 403 = false := by decide +kernel
theorem doorAt403 : soko1_2.board.doors.contains 403 = false := by decide +kernel
theorem trapAt403 : soko1_2.board.rollingTraps.contains 403 = false := by decide +kernel
theorem boxAt403 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 403 = false := rfl
theorem holeAt403 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 403 = false := rfl
theorem advanceAt403_north : advance soko1_2.board 403 .north = some 377 := by decide +kernel
theorem advanceAt403_south : advance soko1_2.board 403 .south = some 429 := by decide +kernel
theorem advanceAt403_east : advance soko1_2.board 403 .east = some 404 := by decide +kernel
theorem advanceAt403_west : advance soko1_2.board 403 .west = some 402 := by decide +kernel
theorem advanceAt403_northEast : advance soko1_2.board 403 .northEast = some 378 := by decide +kernel
theorem advanceAt403_northWest : advance soko1_2.board 403 .northWest = some 376 := by decide +kernel
theorem advanceAt403_southEast : advance soko1_2.board 403 .southEast = some 430 := by decide +kernel
theorem advanceAt403_southWest : advance soko1_2.board 403 .southWest = some 428 := by decide +kernel
theorem floorAt404 : soko1_2.board.floor.contains 404 = false := by decide +kernel
theorem doorAt404 : soko1_2.board.doors.contains 404 = false := by decide +kernel
theorem trapAt404 : soko1_2.board.rollingTraps.contains 404 = false := by decide +kernel
theorem boxAt404 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 404 = false := rfl
theorem holeAt404 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 404 = false := rfl
theorem advanceAt404_north : advance soko1_2.board 404 .north = some 378 := by decide +kernel
theorem advanceAt404_south : advance soko1_2.board 404 .south = some 430 := by decide +kernel
theorem advanceAt404_east : advance soko1_2.board 404 .east = some 405 := by decide +kernel
theorem advanceAt404_west : advance soko1_2.board 404 .west = some 403 := by decide +kernel
theorem advanceAt404_northEast : advance soko1_2.board 404 .northEast = some 379 := by decide +kernel
theorem advanceAt404_northWest : advance soko1_2.board 404 .northWest = some 377 := by decide +kernel
theorem advanceAt404_southEast : advance soko1_2.board 404 .southEast = some 431 := by decide +kernel
theorem advanceAt404_southWest : advance soko1_2.board 404 .southWest = some 429 := by decide +kernel
theorem floorAt405 : soko1_2.board.floor.contains 405 = false := by decide +kernel
theorem doorAt405 : soko1_2.board.doors.contains 405 = false := by decide +kernel
theorem trapAt405 : soko1_2.board.rollingTraps.contains 405 = false := by decide +kernel
theorem boxAt405 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 405 = false := rfl
theorem holeAt405 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 405 = false := rfl
theorem advanceAt405_north : advance soko1_2.board 405 .north = some 379 := by decide +kernel
theorem advanceAt405_south : advance soko1_2.board 405 .south = some 431 := by decide +kernel
theorem advanceAt405_east : advance soko1_2.board 405 .east = some 406 := by decide +kernel
theorem advanceAt405_west : advance soko1_2.board 405 .west = some 404 := by decide +kernel
theorem advanceAt405_northEast : advance soko1_2.board 405 .northEast = some 380 := by decide +kernel
theorem advanceAt405_northWest : advance soko1_2.board 405 .northWest = some 378 := by decide +kernel
theorem advanceAt405_southEast : advance soko1_2.board 405 .southEast = some 432 := by decide +kernel
theorem advanceAt405_southWest : advance soko1_2.board 405 .southWest = some 430 := by decide +kernel
theorem floorAt406 : soko1_2.board.floor.contains 406 = false := by decide +kernel
theorem doorAt406 : soko1_2.board.doors.contains 406 = false := by decide +kernel
theorem trapAt406 : soko1_2.board.rollingTraps.contains 406 = false := by decide +kernel
theorem boxAt406 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 406 = false := rfl
theorem holeAt406 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 406 = false := rfl
theorem advanceAt406_north : advance soko1_2.board 406 .north = some 380 := by decide +kernel
theorem advanceAt406_south : advance soko1_2.board 406 .south = some 432 := by decide +kernel
theorem advanceAt406_east : advance soko1_2.board 406 .east = some 407 := by decide +kernel
theorem advanceAt406_west : advance soko1_2.board 406 .west = some 405 := by decide +kernel
theorem advanceAt406_northEast : advance soko1_2.board 406 .northEast = some 381 := by decide +kernel
theorem advanceAt406_northWest : advance soko1_2.board 406 .northWest = some 379 := by decide +kernel
theorem advanceAt406_southEast : advance soko1_2.board 406 .southEast = some 433 := by decide +kernel
theorem advanceAt406_southWest : advance soko1_2.board 406 .southWest = some 431 := by decide +kernel
theorem floorAt407 : soko1_2.board.floor.contains 407 = false := by decide +kernel
theorem doorAt407 : soko1_2.board.doors.contains 407 = false := by decide +kernel
theorem trapAt407 : soko1_2.board.rollingTraps.contains 407 = false := by decide +kernel
theorem boxAt407 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 407 = false := rfl
theorem holeAt407 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 407 = false := rfl
theorem advanceAt407_north : advance soko1_2.board 407 .north = some 381 := by decide +kernel
theorem advanceAt407_south : advance soko1_2.board 407 .south = some 433 := by decide +kernel
theorem advanceAt407_east : advance soko1_2.board 407 .east = some 408 := by decide +kernel
theorem advanceAt407_west : advance soko1_2.board 407 .west = some 406 := by decide +kernel
theorem advanceAt407_northEast : advance soko1_2.board 407 .northEast = some 382 := by decide +kernel
theorem advanceAt407_northWest : advance soko1_2.board 407 .northWest = some 380 := by decide +kernel
theorem advanceAt407_southEast : advance soko1_2.board 407 .southEast = some 434 := by decide +kernel
theorem advanceAt407_southWest : advance soko1_2.board 407 .southWest = some 432 := by decide +kernel
theorem floorAt408 : soko1_2.board.floor.contains 408 = true := by decide +kernel
theorem doorAt408 : soko1_2.board.doors.contains 408 = false := by decide +kernel
theorem trapAt408 : soko1_2.board.rollingTraps.contains 408 = false := by decide +kernel
theorem boxAt408 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 408 = false := rfl
theorem holeAt408 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 408 = false := rfl
theorem advanceAt408_north : advance soko1_2.board 408 .north = some 382 := by decide +kernel
theorem advanceAt408_south : advance soko1_2.board 408 .south = some 434 := by decide +kernel
theorem advanceAt408_east : advance soko1_2.board 408 .east = some 409 := by decide +kernel
theorem advanceAt408_west : advance soko1_2.board 408 .west = some 407 := by decide +kernel
theorem advanceAt408_northEast : advance soko1_2.board 408 .northEast = some 383 := by decide +kernel
theorem advanceAt408_northWest : advance soko1_2.board 408 .northWest = some 381 := by decide +kernel
theorem advanceAt408_southEast : advance soko1_2.board 408 .southEast = some 435 := by decide +kernel
theorem advanceAt408_southWest : advance soko1_2.board 408 .southWest = some 433 := by decide +kernel
theorem floorAt409 : soko1_2.board.floor.contains 409 = true := by decide +kernel
theorem doorAt409 : soko1_2.board.doors.contains 409 = false := by decide +kernel
theorem trapAt409 : soko1_2.board.rollingTraps.contains 409 = false := by decide +kernel
theorem boxAt409 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 409 = false := rfl
theorem holeAt409 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 409 = false := rfl
theorem advanceAt409_north : advance soko1_2.board 409 .north = some 383 := by decide +kernel
theorem advanceAt409_south : advance soko1_2.board 409 .south = some 435 := by decide +kernel
theorem advanceAt409_east : advance soko1_2.board 409 .east = some 410 := by decide +kernel
theorem advanceAt409_west : advance soko1_2.board 409 .west = some 408 := by decide +kernel
theorem advanceAt409_northEast : advance soko1_2.board 409 .northEast = some 384 := by decide +kernel
theorem advanceAt409_northWest : advance soko1_2.board 409 .northWest = some 382 := by decide +kernel
theorem advanceAt409_southEast : advance soko1_2.board 409 .southEast = some 436 := by decide +kernel
theorem advanceAt409_southWest : advance soko1_2.board 409 .southWest = some 434 := by decide +kernel
theorem floorAt410 : soko1_2.board.floor.contains 410 = true := by decide +kernel
theorem doorAt410 : soko1_2.board.doors.contains 410 = false := by decide +kernel
theorem trapAt410 : soko1_2.board.rollingTraps.contains 410 = false := by decide +kernel
theorem boxAt410 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 410 = false := rfl
theorem holeAt410 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 410 = false := rfl
theorem advanceAt410_north : advance soko1_2.board 410 .north = some 384 := by decide +kernel
theorem advanceAt410_south : advance soko1_2.board 410 .south = some 436 := by decide +kernel
theorem advanceAt410_east : advance soko1_2.board 410 .east = some 411 := by decide +kernel
theorem advanceAt410_west : advance soko1_2.board 410 .west = some 409 := by decide +kernel
theorem advanceAt410_northEast : advance soko1_2.board 410 .northEast = some 385 := by decide +kernel
theorem advanceAt410_northWest : advance soko1_2.board 410 .northWest = some 383 := by decide +kernel
theorem advanceAt410_southEast : advance soko1_2.board 410 .southEast = some 437 := by decide +kernel
theorem advanceAt410_southWest : advance soko1_2.board 410 .southWest = some 435 := by decide +kernel
theorem floorAt411 : soko1_2.board.floor.contains 411 = true := by decide +kernel
theorem doorAt411 : soko1_2.board.doors.contains 411 = false := by decide +kernel
theorem trapAt411 : soko1_2.board.rollingTraps.contains 411 = false := by decide +kernel
theorem boxAt411 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 411 = false := rfl
theorem holeAt411 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 411 = false := rfl
theorem advanceAt411_north : advance soko1_2.board 411 .north = some 385 := by decide +kernel
theorem advanceAt411_south : advance soko1_2.board 411 .south = some 437 := by decide +kernel
theorem advanceAt411_east : advance soko1_2.board 411 .east = some 412 := by decide +kernel
theorem advanceAt411_west : advance soko1_2.board 411 .west = some 410 := by decide +kernel
theorem advanceAt411_northEast : advance soko1_2.board 411 .northEast = some 386 := by decide +kernel
theorem advanceAt411_northWest : advance soko1_2.board 411 .northWest = some 384 := by decide +kernel
theorem advanceAt411_southEast : advance soko1_2.board 411 .southEast = some 438 := by decide +kernel
theorem advanceAt411_southWest : advance soko1_2.board 411 .southWest = some 436 := by decide +kernel
theorem floorAt412 : soko1_2.board.floor.contains 412 = true := by decide +kernel
theorem doorAt412 : soko1_2.board.doors.contains 412 = false := by decide +kernel
theorem trapAt412 : soko1_2.board.rollingTraps.contains 412 = false := by decide +kernel
theorem boxAt412 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 412 = false := rfl
theorem holeAt412 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 412 = false := rfl
theorem advanceAt412_north : advance soko1_2.board 412 .north = some 386 := by decide +kernel
theorem advanceAt412_south : advance soko1_2.board 412 .south = some 438 := by decide +kernel
theorem advanceAt412_east : advance soko1_2.board 412 .east = some 413 := by decide +kernel
theorem advanceAt412_west : advance soko1_2.board 412 .west = some 411 := by decide +kernel
theorem advanceAt412_northEast : advance soko1_2.board 412 .northEast = some 387 := by decide +kernel
theorem advanceAt412_northWest : advance soko1_2.board 412 .northWest = some 385 := by decide +kernel
theorem advanceAt412_southEast : advance soko1_2.board 412 .southEast = some 439 := by decide +kernel
theorem advanceAt412_southWest : advance soko1_2.board 412 .southWest = some 437 := by decide +kernel
theorem floorAt413 : soko1_2.board.floor.contains 413 = false := by decide +kernel
theorem doorAt413 : soko1_2.board.doors.contains 413 = false := by decide +kernel
theorem trapAt413 : soko1_2.board.rollingTraps.contains 413 = false := by decide +kernel
theorem boxAt413 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 413 = false := rfl
theorem holeAt413 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 413 = false := rfl
theorem advanceAt413_north : advance soko1_2.board 413 .north = some 387 := by decide +kernel
theorem advanceAt413_south : advance soko1_2.board 413 .south = some 439 := by decide +kernel
theorem advanceAt413_east : advance soko1_2.board 413 .east = some 414 := by decide +kernel
theorem advanceAt413_west : advance soko1_2.board 413 .west = some 412 := by decide +kernel
theorem advanceAt413_northEast : advance soko1_2.board 413 .northEast = some 388 := by decide +kernel
theorem advanceAt413_northWest : advance soko1_2.board 413 .northWest = some 386 := by decide +kernel
theorem advanceAt413_southEast : advance soko1_2.board 413 .southEast = some 440 := by decide +kernel
theorem advanceAt413_southWest : advance soko1_2.board 413 .southWest = some 438 := by decide +kernel
theorem floorAt414 : soko1_2.board.floor.contains 414 = false := by decide +kernel
theorem doorAt414 : soko1_2.board.doors.contains 414 = false := by decide +kernel
theorem trapAt414 : soko1_2.board.rollingTraps.contains 414 = false := by decide +kernel
theorem boxAt414 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 414 = false := rfl
theorem holeAt414 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 414 = false := rfl
theorem advanceAt414_north : advance soko1_2.board 414 .north = some 388 := by decide +kernel
theorem advanceAt414_south : advance soko1_2.board 414 .south = some 440 := by decide +kernel
theorem advanceAt414_east : advance soko1_2.board 414 .east = some 415 := by decide +kernel
theorem advanceAt414_west : advance soko1_2.board 414 .west = some 413 := by decide +kernel
theorem advanceAt414_northEast : advance soko1_2.board 414 .northEast = some 389 := by decide +kernel
theorem advanceAt414_northWest : advance soko1_2.board 414 .northWest = some 387 := by decide +kernel
theorem advanceAt414_southEast : advance soko1_2.board 414 .southEast = some 441 := by decide +kernel
theorem advanceAt414_southWest : advance soko1_2.board 414 .southWest = some 439 := by decide +kernel
theorem floorAt415 : soko1_2.board.floor.contains 415 = false := by decide +kernel
theorem doorAt415 : soko1_2.board.doors.contains 415 = false := by decide +kernel
theorem trapAt415 : soko1_2.board.rollingTraps.contains 415 = false := by decide +kernel
theorem boxAt415 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 415 = false := rfl
theorem holeAt415 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 415 = false := rfl
theorem advanceAt415_north : advance soko1_2.board 415 .north = some 389 := by decide +kernel
theorem advanceAt415_south : advance soko1_2.board 415 .south = some 441 := by decide +kernel
theorem advanceAt415_east : advance soko1_2.board 415 .east = none := by decide +kernel
theorem advanceAt415_west : advance soko1_2.board 415 .west = some 414 := by decide +kernel
theorem advanceAt415_northEast : advance soko1_2.board 415 .northEast = none := by decide +kernel
theorem advanceAt415_northWest : advance soko1_2.board 415 .northWest = some 388 := by decide +kernel
theorem advanceAt415_southEast : advance soko1_2.board 415 .southEast = none := by decide +kernel
theorem advanceAt415_southWest : advance soko1_2.board 415 .southWest = some 440 := by decide +kernel
theorem floorAt416 : soko1_2.board.floor.contains 416 = false := by decide +kernel
theorem doorAt416 : soko1_2.board.doors.contains 416 = false := by decide +kernel
theorem trapAt416 : soko1_2.board.rollingTraps.contains 416 = false := by decide +kernel
theorem boxAt416 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 416 = false := rfl
theorem holeAt416 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 416 = false := rfl
theorem advanceAt416_north : advance soko1_2.board 416 .north = some 390 := by decide +kernel
theorem advanceAt416_south : advance soko1_2.board 416 .south = none := by decide +kernel
theorem advanceAt416_east : advance soko1_2.board 416 .east = some 417 := by decide +kernel
theorem advanceAt416_west : advance soko1_2.board 416 .west = none := by decide +kernel
theorem advanceAt416_northEast : advance soko1_2.board 416 .northEast = some 391 := by decide +kernel
theorem advanceAt416_northWest : advance soko1_2.board 416 .northWest = none := by decide +kernel
theorem advanceAt416_southEast : advance soko1_2.board 416 .southEast = none := by decide +kernel
theorem advanceAt416_southWest : advance soko1_2.board 416 .southWest = none := by decide +kernel
theorem floorAt417 : soko1_2.board.floor.contains 417 = false := by decide +kernel
theorem doorAt417 : soko1_2.board.doors.contains 417 = false := by decide +kernel
theorem trapAt417 : soko1_2.board.rollingTraps.contains 417 = false := by decide +kernel
theorem boxAt417 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 417 = false := rfl
theorem holeAt417 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 417 = false := rfl
theorem advanceAt417_north : advance soko1_2.board 417 .north = some 391 := by decide +kernel
theorem advanceAt417_south : advance soko1_2.board 417 .south = none := by decide +kernel
theorem advanceAt417_east : advance soko1_2.board 417 .east = some 418 := by decide +kernel
theorem advanceAt417_west : advance soko1_2.board 417 .west = some 416 := by decide +kernel
theorem advanceAt417_northEast : advance soko1_2.board 417 .northEast = some 392 := by decide +kernel
theorem advanceAt417_northWest : advance soko1_2.board 417 .northWest = some 390 := by decide +kernel
theorem advanceAt417_southEast : advance soko1_2.board 417 .southEast = none := by decide +kernel
theorem advanceAt417_southWest : advance soko1_2.board 417 .southWest = none := by decide +kernel
theorem floorAt418 : soko1_2.board.floor.contains 418 = false := by decide +kernel
theorem doorAt418 : soko1_2.board.doors.contains 418 = false := by decide +kernel
theorem trapAt418 : soko1_2.board.rollingTraps.contains 418 = false := by decide +kernel
theorem boxAt418 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 418 = false := rfl
theorem holeAt418 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 418 = false := rfl
theorem advanceAt418_north : advance soko1_2.board 418 .north = some 392 := by decide +kernel
theorem advanceAt418_south : advance soko1_2.board 418 .south = none := by decide +kernel
theorem advanceAt418_east : advance soko1_2.board 418 .east = some 419 := by decide +kernel
theorem advanceAt418_west : advance soko1_2.board 418 .west = some 417 := by decide +kernel
theorem advanceAt418_northEast : advance soko1_2.board 418 .northEast = some 393 := by decide +kernel
theorem advanceAt418_northWest : advance soko1_2.board 418 .northWest = some 391 := by decide +kernel
theorem advanceAt418_southEast : advance soko1_2.board 418 .southEast = none := by decide +kernel
theorem advanceAt418_southWest : advance soko1_2.board 418 .southWest = none := by decide +kernel
theorem floorAt419 : soko1_2.board.floor.contains 419 = false := by decide +kernel
theorem doorAt419 : soko1_2.board.doors.contains 419 = false := by decide +kernel
theorem trapAt419 : soko1_2.board.rollingTraps.contains 419 = false := by decide +kernel
theorem boxAt419 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 419 = false := rfl
theorem holeAt419 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 419 = false := rfl
theorem advanceAt419_north : advance soko1_2.board 419 .north = some 393 := by decide +kernel
theorem advanceAt419_south : advance soko1_2.board 419 .south = none := by decide +kernel
theorem advanceAt419_east : advance soko1_2.board 419 .east = some 420 := by decide +kernel
theorem advanceAt419_west : advance soko1_2.board 419 .west = some 418 := by decide +kernel
theorem advanceAt419_northEast : advance soko1_2.board 419 .northEast = some 394 := by decide +kernel
theorem advanceAt419_northWest : advance soko1_2.board 419 .northWest = some 392 := by decide +kernel
theorem advanceAt419_southEast : advance soko1_2.board 419 .southEast = none := by decide +kernel
theorem advanceAt419_southWest : advance soko1_2.board 419 .southWest = none := by decide +kernel
theorem floorAt420 : soko1_2.board.floor.contains 420 = false := by decide +kernel
theorem doorAt420 : soko1_2.board.doors.contains 420 = false := by decide +kernel
theorem trapAt420 : soko1_2.board.rollingTraps.contains 420 = false := by decide +kernel
theorem boxAt420 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 420 = false := rfl
theorem holeAt420 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 420 = false := rfl
theorem advanceAt420_north : advance soko1_2.board 420 .north = some 394 := by decide +kernel
theorem advanceAt420_south : advance soko1_2.board 420 .south = none := by decide +kernel
theorem advanceAt420_east : advance soko1_2.board 420 .east = some 421 := by decide +kernel
theorem advanceAt420_west : advance soko1_2.board 420 .west = some 419 := by decide +kernel
theorem advanceAt420_northEast : advance soko1_2.board 420 .northEast = some 395 := by decide +kernel
theorem advanceAt420_northWest : advance soko1_2.board 420 .northWest = some 393 := by decide +kernel
theorem advanceAt420_southEast : advance soko1_2.board 420 .southEast = none := by decide +kernel
theorem advanceAt420_southWest : advance soko1_2.board 420 .southWest = none := by decide +kernel
theorem floorAt421 : soko1_2.board.floor.contains 421 = false := by decide +kernel
theorem doorAt421 : soko1_2.board.doors.contains 421 = false := by decide +kernel
theorem trapAt421 : soko1_2.board.rollingTraps.contains 421 = false := by decide +kernel
theorem boxAt421 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 421 = false := rfl
theorem holeAt421 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 421 = false := rfl
theorem advanceAt421_north : advance soko1_2.board 421 .north = some 395 := by decide +kernel
theorem advanceAt421_south : advance soko1_2.board 421 .south = none := by decide +kernel
theorem advanceAt421_east : advance soko1_2.board 421 .east = some 422 := by decide +kernel
theorem advanceAt421_west : advance soko1_2.board 421 .west = some 420 := by decide +kernel
theorem advanceAt421_northEast : advance soko1_2.board 421 .northEast = some 396 := by decide +kernel
theorem advanceAt421_northWest : advance soko1_2.board 421 .northWest = some 394 := by decide +kernel
theorem advanceAt421_southEast : advance soko1_2.board 421 .southEast = none := by decide +kernel
theorem advanceAt421_southWest : advance soko1_2.board 421 .southWest = none := by decide +kernel
theorem floorAt422 : soko1_2.board.floor.contains 422 = false := by decide +kernel
theorem doorAt422 : soko1_2.board.doors.contains 422 = false := by decide +kernel
theorem trapAt422 : soko1_2.board.rollingTraps.contains 422 = false := by decide +kernel
theorem boxAt422 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 422 = false := rfl
theorem holeAt422 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 422 = false := rfl
theorem advanceAt422_north : advance soko1_2.board 422 .north = some 396 := by decide +kernel
theorem advanceAt422_south : advance soko1_2.board 422 .south = none := by decide +kernel
theorem advanceAt422_east : advance soko1_2.board 422 .east = some 423 := by decide +kernel
theorem advanceAt422_west : advance soko1_2.board 422 .west = some 421 := by decide +kernel
theorem advanceAt422_northEast : advance soko1_2.board 422 .northEast = some 397 := by decide +kernel
theorem advanceAt422_northWest : advance soko1_2.board 422 .northWest = some 395 := by decide +kernel
theorem advanceAt422_southEast : advance soko1_2.board 422 .southEast = none := by decide +kernel
theorem advanceAt422_southWest : advance soko1_2.board 422 .southWest = none := by decide +kernel
theorem floorAt423 : soko1_2.board.floor.contains 423 = false := by decide +kernel
theorem doorAt423 : soko1_2.board.doors.contains 423 = false := by decide +kernel
theorem trapAt423 : soko1_2.board.rollingTraps.contains 423 = false := by decide +kernel
theorem boxAt423 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 423 = false := rfl
theorem holeAt423 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 423 = false := rfl
theorem advanceAt423_north : advance soko1_2.board 423 .north = some 397 := by decide +kernel
theorem advanceAt423_south : advance soko1_2.board 423 .south = none := by decide +kernel
theorem advanceAt423_east : advance soko1_2.board 423 .east = some 424 := by decide +kernel
theorem advanceAt423_west : advance soko1_2.board 423 .west = some 422 := by decide +kernel
theorem advanceAt423_northEast : advance soko1_2.board 423 .northEast = some 398 := by decide +kernel
theorem advanceAt423_northWest : advance soko1_2.board 423 .northWest = some 396 := by decide +kernel
theorem advanceAt423_southEast : advance soko1_2.board 423 .southEast = none := by decide +kernel
theorem advanceAt423_southWest : advance soko1_2.board 423 .southWest = none := by decide +kernel
theorem floorAt424 : soko1_2.board.floor.contains 424 = false := by decide +kernel
theorem doorAt424 : soko1_2.board.doors.contains 424 = false := by decide +kernel
theorem trapAt424 : soko1_2.board.rollingTraps.contains 424 = false := by decide +kernel
theorem boxAt424 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 424 = false := rfl
theorem holeAt424 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 424 = false := rfl
theorem advanceAt424_north : advance soko1_2.board 424 .north = some 398 := by decide +kernel
theorem advanceAt424_south : advance soko1_2.board 424 .south = none := by decide +kernel
theorem advanceAt424_east : advance soko1_2.board 424 .east = some 425 := by decide +kernel
theorem advanceAt424_west : advance soko1_2.board 424 .west = some 423 := by decide +kernel
theorem advanceAt424_northEast : advance soko1_2.board 424 .northEast = some 399 := by decide +kernel
theorem advanceAt424_northWest : advance soko1_2.board 424 .northWest = some 397 := by decide +kernel
theorem advanceAt424_southEast : advance soko1_2.board 424 .southEast = none := by decide +kernel
theorem advanceAt424_southWest : advance soko1_2.board 424 .southWest = none := by decide +kernel
theorem floorAt425 : soko1_2.board.floor.contains 425 = false := by decide +kernel
theorem doorAt425 : soko1_2.board.doors.contains 425 = false := by decide +kernel
theorem trapAt425 : soko1_2.board.rollingTraps.contains 425 = false := by decide +kernel
theorem boxAt425 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 425 = false := rfl
theorem holeAt425 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 425 = false := rfl
theorem advanceAt425_north : advance soko1_2.board 425 .north = some 399 := by decide +kernel
theorem advanceAt425_south : advance soko1_2.board 425 .south = none := by decide +kernel
theorem advanceAt425_east : advance soko1_2.board 425 .east = some 426 := by decide +kernel
theorem advanceAt425_west : advance soko1_2.board 425 .west = some 424 := by decide +kernel
theorem advanceAt425_northEast : advance soko1_2.board 425 .northEast = some 400 := by decide +kernel
theorem advanceAt425_northWest : advance soko1_2.board 425 .northWest = some 398 := by decide +kernel
theorem advanceAt425_southEast : advance soko1_2.board 425 .southEast = none := by decide +kernel
theorem advanceAt425_southWest : advance soko1_2.board 425 .southWest = none := by decide +kernel
theorem floorAt426 : soko1_2.board.floor.contains 426 = false := by decide +kernel
theorem doorAt426 : soko1_2.board.doors.contains 426 = false := by decide +kernel
theorem trapAt426 : soko1_2.board.rollingTraps.contains 426 = false := by decide +kernel
theorem boxAt426 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 426 = false := rfl
theorem holeAt426 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 426 = false := rfl
theorem advanceAt426_north : advance soko1_2.board 426 .north = some 400 := by decide +kernel
theorem advanceAt426_south : advance soko1_2.board 426 .south = none := by decide +kernel
theorem advanceAt426_east : advance soko1_2.board 426 .east = some 427 := by decide +kernel
theorem advanceAt426_west : advance soko1_2.board 426 .west = some 425 := by decide +kernel
theorem advanceAt426_northEast : advance soko1_2.board 426 .northEast = some 401 := by decide +kernel
theorem advanceAt426_northWest : advance soko1_2.board 426 .northWest = some 399 := by decide +kernel
theorem advanceAt426_southEast : advance soko1_2.board 426 .southEast = none := by decide +kernel
theorem advanceAt426_southWest : advance soko1_2.board 426 .southWest = none := by decide +kernel
theorem floorAt427 : soko1_2.board.floor.contains 427 = false := by decide +kernel
theorem doorAt427 : soko1_2.board.doors.contains 427 = false := by decide +kernel
theorem trapAt427 : soko1_2.board.rollingTraps.contains 427 = false := by decide +kernel
theorem boxAt427 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 427 = false := rfl
theorem holeAt427 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 427 = false := rfl
theorem advanceAt427_north : advance soko1_2.board 427 .north = some 401 := by decide +kernel
theorem advanceAt427_south : advance soko1_2.board 427 .south = none := by decide +kernel
theorem advanceAt427_east : advance soko1_2.board 427 .east = some 428 := by decide +kernel
theorem advanceAt427_west : advance soko1_2.board 427 .west = some 426 := by decide +kernel
theorem advanceAt427_northEast : advance soko1_2.board 427 .northEast = some 402 := by decide +kernel
theorem advanceAt427_northWest : advance soko1_2.board 427 .northWest = some 400 := by decide +kernel
theorem advanceAt427_southEast : advance soko1_2.board 427 .southEast = none := by decide +kernel
theorem advanceAt427_southWest : advance soko1_2.board 427 .southWest = none := by decide +kernel
theorem floorAt428 : soko1_2.board.floor.contains 428 = false := by decide +kernel
theorem doorAt428 : soko1_2.board.doors.contains 428 = false := by decide +kernel
theorem trapAt428 : soko1_2.board.rollingTraps.contains 428 = false := by decide +kernel
theorem boxAt428 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 428 = false := rfl
theorem holeAt428 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 428 = false := rfl
theorem advanceAt428_north : advance soko1_2.board 428 .north = some 402 := by decide +kernel
theorem advanceAt428_south : advance soko1_2.board 428 .south = none := by decide +kernel
theorem advanceAt428_east : advance soko1_2.board 428 .east = some 429 := by decide +kernel
theorem advanceAt428_west : advance soko1_2.board 428 .west = some 427 := by decide +kernel
theorem advanceAt428_northEast : advance soko1_2.board 428 .northEast = some 403 := by decide +kernel
theorem advanceAt428_northWest : advance soko1_2.board 428 .northWest = some 401 := by decide +kernel
theorem advanceAt428_southEast : advance soko1_2.board 428 .southEast = none := by decide +kernel
theorem advanceAt428_southWest : advance soko1_2.board 428 .southWest = none := by decide +kernel
theorem floorAt429 : soko1_2.board.floor.contains 429 = false := by decide +kernel
theorem doorAt429 : soko1_2.board.doors.contains 429 = false := by decide +kernel
theorem trapAt429 : soko1_2.board.rollingTraps.contains 429 = false := by decide +kernel
theorem boxAt429 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 429 = false := rfl
theorem holeAt429 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 429 = false := rfl
theorem advanceAt429_north : advance soko1_2.board 429 .north = some 403 := by decide +kernel
theorem advanceAt429_south : advance soko1_2.board 429 .south = none := by decide +kernel
theorem advanceAt429_east : advance soko1_2.board 429 .east = some 430 := by decide +kernel
theorem advanceAt429_west : advance soko1_2.board 429 .west = some 428 := by decide +kernel
theorem advanceAt429_northEast : advance soko1_2.board 429 .northEast = some 404 := by decide +kernel
theorem advanceAt429_northWest : advance soko1_2.board 429 .northWest = some 402 := by decide +kernel
theorem advanceAt429_southEast : advance soko1_2.board 429 .southEast = none := by decide +kernel
theorem advanceAt429_southWest : advance soko1_2.board 429 .southWest = none := by decide +kernel
theorem floorAt430 : soko1_2.board.floor.contains 430 = false := by decide +kernel
theorem doorAt430 : soko1_2.board.doors.contains 430 = false := by decide +kernel
theorem trapAt430 : soko1_2.board.rollingTraps.contains 430 = false := by decide +kernel
theorem boxAt430 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 430 = false := rfl
theorem holeAt430 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 430 = false := rfl
theorem advanceAt430_north : advance soko1_2.board 430 .north = some 404 := by decide +kernel
theorem advanceAt430_south : advance soko1_2.board 430 .south = none := by decide +kernel
theorem advanceAt430_east : advance soko1_2.board 430 .east = some 431 := by decide +kernel
theorem advanceAt430_west : advance soko1_2.board 430 .west = some 429 := by decide +kernel
theorem advanceAt430_northEast : advance soko1_2.board 430 .northEast = some 405 := by decide +kernel
theorem advanceAt430_northWest : advance soko1_2.board 430 .northWest = some 403 := by decide +kernel
theorem advanceAt430_southEast : advance soko1_2.board 430 .southEast = none := by decide +kernel
theorem advanceAt430_southWest : advance soko1_2.board 430 .southWest = none := by decide +kernel
theorem floorAt431 : soko1_2.board.floor.contains 431 = false := by decide +kernel
theorem doorAt431 : soko1_2.board.doors.contains 431 = false := by decide +kernel
theorem trapAt431 : soko1_2.board.rollingTraps.contains 431 = false := by decide +kernel
theorem boxAt431 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 431 = false := rfl
theorem holeAt431 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 431 = false := rfl
theorem advanceAt431_north : advance soko1_2.board 431 .north = some 405 := by decide +kernel
theorem advanceAt431_south : advance soko1_2.board 431 .south = none := by decide +kernel
theorem advanceAt431_east : advance soko1_2.board 431 .east = some 432 := by decide +kernel
theorem advanceAt431_west : advance soko1_2.board 431 .west = some 430 := by decide +kernel
theorem advanceAt431_northEast : advance soko1_2.board 431 .northEast = some 406 := by decide +kernel
theorem advanceAt431_northWest : advance soko1_2.board 431 .northWest = some 404 := by decide +kernel
theorem advanceAt431_southEast : advance soko1_2.board 431 .southEast = none := by decide +kernel
theorem advanceAt431_southWest : advance soko1_2.board 431 .southWest = none := by decide +kernel
theorem floorAt432 : soko1_2.board.floor.contains 432 = false := by decide +kernel
theorem doorAt432 : soko1_2.board.doors.contains 432 = false := by decide +kernel
theorem trapAt432 : soko1_2.board.rollingTraps.contains 432 = false := by decide +kernel
theorem boxAt432 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 432 = false := rfl
theorem holeAt432 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 432 = false := rfl
theorem advanceAt432_north : advance soko1_2.board 432 .north = some 406 := by decide +kernel
theorem advanceAt432_south : advance soko1_2.board 432 .south = none := by decide +kernel
theorem advanceAt432_east : advance soko1_2.board 432 .east = some 433 := by decide +kernel
theorem advanceAt432_west : advance soko1_2.board 432 .west = some 431 := by decide +kernel
theorem advanceAt432_northEast : advance soko1_2.board 432 .northEast = some 407 := by decide +kernel
theorem advanceAt432_northWest : advance soko1_2.board 432 .northWest = some 405 := by decide +kernel
theorem advanceAt432_southEast : advance soko1_2.board 432 .southEast = none := by decide +kernel
theorem advanceAt432_southWest : advance soko1_2.board 432 .southWest = none := by decide +kernel
theorem floorAt433 : soko1_2.board.floor.contains 433 = false := by decide +kernel
theorem doorAt433 : soko1_2.board.doors.contains 433 = false := by decide +kernel
theorem trapAt433 : soko1_2.board.rollingTraps.contains 433 = false := by decide +kernel
theorem boxAt433 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 433 = false := rfl
theorem holeAt433 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 433 = false := rfl
theorem advanceAt433_north : advance soko1_2.board 433 .north = some 407 := by decide +kernel
theorem advanceAt433_south : advance soko1_2.board 433 .south = none := by decide +kernel
theorem advanceAt433_east : advance soko1_2.board 433 .east = some 434 := by decide +kernel
theorem advanceAt433_west : advance soko1_2.board 433 .west = some 432 := by decide +kernel
theorem advanceAt433_northEast : advance soko1_2.board 433 .northEast = some 408 := by decide +kernel
theorem advanceAt433_northWest : advance soko1_2.board 433 .northWest = some 406 := by decide +kernel
theorem advanceAt433_southEast : advance soko1_2.board 433 .southEast = none := by decide +kernel
theorem advanceAt433_southWest : advance soko1_2.board 433 .southWest = none := by decide +kernel
theorem floorAt434 : soko1_2.board.floor.contains 434 = false := by decide +kernel
theorem doorAt434 : soko1_2.board.doors.contains 434 = false := by decide +kernel
theorem trapAt434 : soko1_2.board.rollingTraps.contains 434 = false := by decide +kernel
theorem boxAt434 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 434 = false := rfl
theorem holeAt434 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 434 = false := rfl
theorem advanceAt434_north : advance soko1_2.board 434 .north = some 408 := by decide +kernel
theorem advanceAt434_south : advance soko1_2.board 434 .south = none := by decide +kernel
theorem advanceAt434_east : advance soko1_2.board 434 .east = some 435 := by decide +kernel
theorem advanceAt434_west : advance soko1_2.board 434 .west = some 433 := by decide +kernel
theorem advanceAt434_northEast : advance soko1_2.board 434 .northEast = some 409 := by decide +kernel
theorem advanceAt434_northWest : advance soko1_2.board 434 .northWest = some 407 := by decide +kernel
theorem advanceAt434_southEast : advance soko1_2.board 434 .southEast = none := by decide +kernel
theorem advanceAt434_southWest : advance soko1_2.board 434 .southWest = none := by decide +kernel
theorem floorAt435 : soko1_2.board.floor.contains 435 = false := by decide +kernel
theorem doorAt435 : soko1_2.board.doors.contains 435 = false := by decide +kernel
theorem trapAt435 : soko1_2.board.rollingTraps.contains 435 = false := by decide +kernel
theorem boxAt435 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 435 = false := rfl
theorem holeAt435 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 435 = false := rfl
theorem advanceAt435_north : advance soko1_2.board 435 .north = some 409 := by decide +kernel
theorem advanceAt435_south : advance soko1_2.board 435 .south = none := by decide +kernel
theorem advanceAt435_east : advance soko1_2.board 435 .east = some 436 := by decide +kernel
theorem advanceAt435_west : advance soko1_2.board 435 .west = some 434 := by decide +kernel
theorem advanceAt435_northEast : advance soko1_2.board 435 .northEast = some 410 := by decide +kernel
theorem advanceAt435_northWest : advance soko1_2.board 435 .northWest = some 408 := by decide +kernel
theorem advanceAt435_southEast : advance soko1_2.board 435 .southEast = none := by decide +kernel
theorem advanceAt435_southWest : advance soko1_2.board 435 .southWest = none := by decide +kernel
theorem floorAt436 : soko1_2.board.floor.contains 436 = false := by decide +kernel
theorem doorAt436 : soko1_2.board.doors.contains 436 = false := by decide +kernel
theorem trapAt436 : soko1_2.board.rollingTraps.contains 436 = false := by decide +kernel
theorem boxAt436 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 436 = false := rfl
theorem holeAt436 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 436 = false := rfl
theorem advanceAt436_north : advance soko1_2.board 436 .north = some 410 := by decide +kernel
theorem advanceAt436_south : advance soko1_2.board 436 .south = none := by decide +kernel
theorem advanceAt436_east : advance soko1_2.board 436 .east = some 437 := by decide +kernel
theorem advanceAt436_west : advance soko1_2.board 436 .west = some 435 := by decide +kernel
theorem advanceAt436_northEast : advance soko1_2.board 436 .northEast = some 411 := by decide +kernel
theorem advanceAt436_northWest : advance soko1_2.board 436 .northWest = some 409 := by decide +kernel
theorem advanceAt436_southEast : advance soko1_2.board 436 .southEast = none := by decide +kernel
theorem advanceAt436_southWest : advance soko1_2.board 436 .southWest = none := by decide +kernel
theorem floorAt437 : soko1_2.board.floor.contains 437 = false := by decide +kernel
theorem doorAt437 : soko1_2.board.doors.contains 437 = false := by decide +kernel
theorem trapAt437 : soko1_2.board.rollingTraps.contains 437 = false := by decide +kernel
theorem boxAt437 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 437 = false := rfl
theorem holeAt437 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 437 = false := rfl
theorem advanceAt437_north : advance soko1_2.board 437 .north = some 411 := by decide +kernel
theorem advanceAt437_south : advance soko1_2.board 437 .south = none := by decide +kernel
theorem advanceAt437_east : advance soko1_2.board 437 .east = some 438 := by decide +kernel
theorem advanceAt437_west : advance soko1_2.board 437 .west = some 436 := by decide +kernel
theorem advanceAt437_northEast : advance soko1_2.board 437 .northEast = some 412 := by decide +kernel
theorem advanceAt437_northWest : advance soko1_2.board 437 .northWest = some 410 := by decide +kernel
theorem advanceAt437_southEast : advance soko1_2.board 437 .southEast = none := by decide +kernel
theorem advanceAt437_southWest : advance soko1_2.board 437 .southWest = none := by decide +kernel
theorem floorAt438 : soko1_2.board.floor.contains 438 = false := by decide +kernel
theorem doorAt438 : soko1_2.board.doors.contains 438 = false := by decide +kernel
theorem trapAt438 : soko1_2.board.rollingTraps.contains 438 = false := by decide +kernel
theorem boxAt438 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 438 = false := rfl
theorem holeAt438 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 438 = false := rfl
theorem advanceAt438_north : advance soko1_2.board 438 .north = some 412 := by decide +kernel
theorem advanceAt438_south : advance soko1_2.board 438 .south = none := by decide +kernel
theorem advanceAt438_east : advance soko1_2.board 438 .east = some 439 := by decide +kernel
theorem advanceAt438_west : advance soko1_2.board 438 .west = some 437 := by decide +kernel
theorem advanceAt438_northEast : advance soko1_2.board 438 .northEast = some 413 := by decide +kernel
theorem advanceAt438_northWest : advance soko1_2.board 438 .northWest = some 411 := by decide +kernel
theorem advanceAt438_southEast : advance soko1_2.board 438 .southEast = none := by decide +kernel
theorem advanceAt438_southWest : advance soko1_2.board 438 .southWest = none := by decide +kernel
theorem floorAt439 : soko1_2.board.floor.contains 439 = false := by decide +kernel
theorem doorAt439 : soko1_2.board.doors.contains 439 = false := by decide +kernel
theorem trapAt439 : soko1_2.board.rollingTraps.contains 439 = false := by decide +kernel
theorem boxAt439 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p 439 = false := rfl
theorem holeAt439 (p : Pattern) : project (soko1_2.initial.holes.drop 5) 439 = false := rfl
theorem advanceAt439_north : advance soko1_2.board 439 .north = some 413 := by decide +kernel
theorem advanceAt439_south : advance soko1_2.board 439 .south = none := by decide +kernel
theorem advanceAt439_east : advance soko1_2.board 439 .east = some 440 := by decide +kernel
theorem advanceAt439_west : advance soko1_2.board 439 .west = some 438 := by decide +kernel
theorem advanceAt439_northEast : advance soko1_2.board 439 .northEast = some 414 := by decide +kernel
theorem advanceAt439_northWest : advance soko1_2.board 439 .northWest = some 412 := by decide +kernel
theorem advanceAt439_southEast : advance soko1_2.board 439 .southEast = none := by decide +kernel
theorem advanceAt439_southWest : advance soko1_2.board 439 .southWest = none := by decide +kernel
end NetHack.Soko12Forward220.Unified.P05
