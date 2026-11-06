import NetHack.Soko12Forward220.Unified.P00.OracleCorners05
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P00
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem cornerAt296_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 296 .north = false := rfl
theorem cornerAt296_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 296 .south = false := rfl
theorem cornerAt296_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 296 .east = false := rfl
theorem cornerAt296_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 296 .west = false := rfl
theorem cornerAt296_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 296 .northEast = (p 270 && p 297) := rfl
theorem cornerAt296_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 296 .northWest = (p 270 && true) := rfl
theorem cornerAt296_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 296 .southEast = (p 322 && p 297) := rfl
theorem cornerAt296_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 296 .southWest = (p 322 && true) := rfl
theorem cornerAt297_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 297 .north = false := rfl
theorem cornerAt297_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 297 .south = false := rfl
theorem cornerAt297_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 297 .east = false := rfl
theorem cornerAt297_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 297 .west = false := rfl
theorem cornerAt297_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 297 .northEast = (p 271 && true) := rfl
theorem cornerAt297_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 297 .northWest = (p 271 && p 296) := rfl
theorem cornerAt297_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 297 .southEast = (true && true) := rfl
theorem cornerAt297_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 297 .southWest = (true && p 296) := rfl
theorem cornerAt317_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 317 .north = false := rfl
theorem cornerAt317_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 317 .south = false := rfl
theorem cornerAt317_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 317 .east = false := rfl
theorem cornerAt317_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 317 .west = false := rfl
theorem cornerAt317_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 317 .northEast = (p 291 && p 318) := rfl
theorem cornerAt317_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 317 .northWest = (p 291 && true) := rfl
theorem cornerAt317_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 317 .southEast = (true && p 318) := rfl
theorem cornerAt317_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 317 .southWest = (true && true) := rfl
theorem cornerAt318_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 318 .north = false := rfl
theorem cornerAt318_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 318 .south = false := rfl
theorem cornerAt318_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 318 .east = false := rfl
theorem cornerAt318_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 318 .west = false := rfl
theorem cornerAt318_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 318 .northEast = (p 292 && p 319) := rfl
theorem cornerAt318_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 318 .northWest = (p 292 && p 317) := rfl
theorem cornerAt318_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 318 .southEast = (true && p 319) := rfl
theorem cornerAt318_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 318 .southWest = (true && p 317) := rfl
theorem cornerAt319_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 319 .north = false := rfl
theorem cornerAt319_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 319 .south = false := rfl
theorem cornerAt319_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 319 .east = false := rfl
theorem cornerAt319_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 319 .west = false := rfl
theorem cornerAt319_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 319 .northEast = (p 293 && p 320) := rfl
theorem cornerAt319_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 319 .northWest = (p 293 && p 318) := rfl
theorem cornerAt319_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 319 .southEast = (p 345 && p 320) := rfl
theorem cornerAt319_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 319 .southWest = (p 345 && p 318) := rfl
theorem cornerAt320_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 320 .north = false := rfl
theorem cornerAt320_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 320 .south = false := rfl
theorem cornerAt320_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 320 .east = false := rfl
theorem cornerAt320_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 320 .west = false := rfl
theorem cornerAt320_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 320 .northEast = (p 294 && true) := rfl
theorem cornerAt320_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 320 .northWest = (p 294 && p 319) := rfl
theorem cornerAt320_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 320 .southEast = (true && true) := rfl
theorem cornerAt320_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 320 .southWest = (true && p 319) := rfl
theorem cornerAt322_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 322 .north = false := rfl
theorem cornerAt322_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 322 .south = false := rfl
theorem cornerAt322_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 322 .east = false := rfl
theorem cornerAt322_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 322 .west = false := rfl
theorem cornerAt322_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 322 .northEast = (p 296 && true) := rfl
theorem cornerAt322_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 322 .northWest = (p 296 && true) := rfl
theorem cornerAt322_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 322 .southEast = (p 348 && true) := rfl
theorem cornerAt322_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 322 .southWest = (p 348 && true) := rfl
theorem cornerAt345_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 345 .north = false := rfl
theorem cornerAt345_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 345 .south = false := rfl
theorem cornerAt345_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 345 .east = false := rfl
theorem cornerAt345_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 345 .west = false := rfl
theorem cornerAt345_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 345 .northEast = (p 319 && true) := rfl
theorem cornerAt345_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 345 .northWest = (p 319 && true) := rfl
theorem cornerAt345_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 345 .southEast = (p 371 && true) := rfl
theorem cornerAt345_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 345 .southWest = (p 371 && true) := rfl
theorem cornerAt348_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 348 .north = false := rfl
theorem cornerAt348_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 348 .south = false := rfl
theorem cornerAt348_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 348 .east = false := rfl
theorem cornerAt348_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 348 .west = false := rfl
theorem cornerAt348_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 348 .northEast = (p 322 && true) := rfl
theorem cornerAt348_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 348 .northWest = (p 322 && true) := rfl
theorem cornerAt348_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 348 .southEast = (p 374 && true) := rfl
theorem cornerAt348_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 348 .southWest = (p 374 && true) := rfl
theorem cornerAt370_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 370 .north = false := rfl
theorem cornerAt370_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 370 .south = false := rfl
theorem cornerAt370_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 370 .east = false := rfl
theorem cornerAt370_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 370 .west = false := rfl
theorem cornerAt370_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 370 .northEast = (true && p 371) := rfl
theorem cornerAt370_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 370 .northWest = (true && true) := rfl
theorem cornerAt370_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 370 .southEast = (false && p 371) := rfl
theorem cornerAt370_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 370 .southWest = (false && true) := rfl
theorem cornerAt371_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 371 .north = false := rfl
theorem cornerAt371_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 371 .south = false := rfl
theorem cornerAt371_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 371 .east = false := rfl
theorem cornerAt371_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 371 .west = false := rfl
theorem cornerAt371_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 371 .northEast = (p 345 && p 372) := rfl
theorem cornerAt371_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 371 .northWest = (p 345 && p 370) := rfl
theorem cornerAt371_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 371 .southEast = (p 397 && p 372) := rfl
theorem cornerAt371_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 371 .southWest = (p 397 && p 370) := rfl
theorem cornerAt372_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 372 .north = false := rfl
theorem cornerAt372_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 372 .south = false := rfl
theorem cornerAt372_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 372 .east = false := rfl
theorem cornerAt372_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 372 .west = false := rfl
theorem cornerAt372_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 372 .northEast = (true && p 373) := rfl
theorem cornerAt372_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 372 .northWest = (true && p 371) := rfl
theorem cornerAt372_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 372 .southEast = (true && p 373) := rfl
theorem cornerAt372_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 372 .southWest = (true && p 371) := rfl
theorem cornerAt373_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 373 .north = false := rfl
theorem cornerAt373_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 373 .south = false := rfl
theorem cornerAt373_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 373 .east = false := rfl
theorem cornerAt373_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 373 .west = false := rfl
end NetHack.Soko12Forward220.Unified.P00
