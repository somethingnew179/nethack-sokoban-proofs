import NetHack.Soko12Forward220.Unified.P05.OracleCorners05
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P05
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem cornerAt290_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 290 .north = false := rfl
theorem cornerAt290_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 290 .south = false := rfl
theorem cornerAt290_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 290 .east = false := rfl
theorem cornerAt290_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 290 .west = false := rfl
theorem cornerAt290_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 290 .northEast = (p 264 && p 291) := rfl
theorem cornerAt290_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 290 .northWest = (p 264 && p 289) := rfl
theorem cornerAt290_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 290 .southEast = (true && p 291) := rfl
theorem cornerAt290_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 290 .southWest = (true && p 289) := rfl
theorem cornerAt291_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 291 .north = false := rfl
theorem cornerAt291_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 291 .south = false := rfl
theorem cornerAt291_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 291 .east = false := rfl
theorem cornerAt291_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 291 .west = false := rfl
theorem cornerAt291_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 291 .northEast = (p 265 && p 292) := rfl
theorem cornerAt291_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 291 .northWest = (p 265 && p 290) := rfl
theorem cornerAt291_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 291 .southEast = (p 317 && p 292) := rfl
theorem cornerAt291_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 291 .southWest = (p 317 && p 290) := rfl
theorem cornerAt292_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 292 .north = false := rfl
theorem cornerAt292_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 292 .south = false := rfl
theorem cornerAt292_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 292 .east = false := rfl
theorem cornerAt292_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 292 .west = false := rfl
theorem cornerAt292_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 292 .northEast = (true && p 293) := rfl
theorem cornerAt292_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 292 .northWest = (true && p 291) := rfl
theorem cornerAt292_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 292 .southEast = (p 318 && p 293) := rfl
theorem cornerAt292_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 292 .southWest = (p 318 && p 291) := rfl
theorem cornerAt293_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 293 .north = false := rfl
theorem cornerAt293_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 293 .south = false := rfl
theorem cornerAt293_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 293 .east = false := rfl
theorem cornerAt293_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 293 .west = false := rfl
theorem cornerAt293_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 293 .northEast = (true && p 294) := rfl
theorem cornerAt293_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 293 .northWest = (true && p 292) := rfl
theorem cornerAt293_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 293 .southEast = (p 319 && p 294) := rfl
theorem cornerAt293_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 293 .southWest = (p 319 && p 292) := rfl
theorem cornerAt294_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 294 .north = false := rfl
theorem cornerAt294_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 294 .south = false := rfl
theorem cornerAt294_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 294 .east = false := rfl
theorem cornerAt294_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 294 .west = false := rfl
theorem cornerAt294_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 294 .northEast = (true && true) := rfl
theorem cornerAt294_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 294 .northWest = (true && p 293) := rfl
theorem cornerAt294_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 294 .southEast = (p 320 && true) := rfl
theorem cornerAt294_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 294 .southWest = (p 320 && p 293) := rfl
theorem cornerAt296_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 296 .north = false := rfl
theorem cornerAt296_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 296 .south = false := rfl
theorem cornerAt296_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 296 .east = false := rfl
theorem cornerAt296_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 296 .west = false := rfl
theorem cornerAt296_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 296 .northEast = (p 270 && p 297) := rfl
theorem cornerAt296_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 296 .northWest = (p 270 && true) := rfl
theorem cornerAt296_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 296 .southEast = (p 322 && p 297) := rfl
theorem cornerAt296_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 296 .southWest = (p 322 && true) := rfl
theorem cornerAt297_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 297 .north = false := rfl
theorem cornerAt297_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 297 .south = false := rfl
theorem cornerAt297_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 297 .east = false := rfl
theorem cornerAt297_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 297 .west = false := rfl
theorem cornerAt297_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 297 .northEast = (p 271 && true) := rfl
theorem cornerAt297_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 297 .northWest = (p 271 && p 296) := rfl
theorem cornerAt297_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 297 .southEast = (true && true) := rfl
theorem cornerAt297_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 297 .southWest = (true && p 296) := rfl
theorem cornerAt317_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 317 .north = false := rfl
theorem cornerAt317_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 317 .south = false := rfl
theorem cornerAt317_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 317 .east = false := rfl
theorem cornerAt317_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 317 .west = false := rfl
theorem cornerAt317_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 317 .northEast = (p 291 && p 318) := rfl
theorem cornerAt317_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 317 .northWest = (p 291 && true) := rfl
theorem cornerAt317_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 317 .southEast = (true && p 318) := rfl
theorem cornerAt317_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 317 .southWest = (true && true) := rfl
theorem cornerAt318_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 318 .north = false := rfl
theorem cornerAt318_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 318 .south = false := rfl
theorem cornerAt318_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 318 .east = false := rfl
theorem cornerAt318_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 318 .west = false := rfl
theorem cornerAt318_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 318 .northEast = (p 292 && p 319) := rfl
theorem cornerAt318_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 318 .northWest = (p 292 && p 317) := rfl
theorem cornerAt318_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 318 .southEast = (true && p 319) := rfl
theorem cornerAt318_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 318 .southWest = (true && p 317) := rfl
theorem cornerAt319_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 319 .north = false := rfl
theorem cornerAt319_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 319 .south = false := rfl
theorem cornerAt319_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 319 .east = false := rfl
theorem cornerAt319_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 319 .west = false := rfl
theorem cornerAt319_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 319 .northEast = (p 293 && p 320) := rfl
theorem cornerAt319_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 319 .northWest = (p 293 && p 318) := rfl
theorem cornerAt319_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 319 .southEast = (p 345 && p 320) := rfl
theorem cornerAt319_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 319 .southWest = (p 345 && p 318) := rfl
theorem cornerAt320_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 320 .north = false := rfl
theorem cornerAt320_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 320 .south = false := rfl
theorem cornerAt320_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 320 .east = false := rfl
theorem cornerAt320_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 320 .west = false := rfl
theorem cornerAt320_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 320 .northEast = (p 294 && true) := rfl
theorem cornerAt320_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 320 .northWest = (p 294 && p 319) := rfl
theorem cornerAt320_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 320 .southEast = (true && true) := rfl
theorem cornerAt320_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 320 .southWest = (true && p 319) := rfl
theorem cornerAt322_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 322 .north = false := rfl
theorem cornerAt322_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 322 .south = false := rfl
theorem cornerAt322_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 322 .east = false := rfl
theorem cornerAt322_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 322 .west = false := rfl
theorem cornerAt322_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 322 .northEast = (p 296 && true) := rfl
theorem cornerAt322_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 322 .northWest = (p 296 && true) := rfl
theorem cornerAt322_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 322 .southEast = (p 348 && true) := rfl
theorem cornerAt322_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 322 .southWest = (p 348 && true) := rfl
theorem cornerAt345_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 345 .north = false := rfl
theorem cornerAt345_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 345 .south = false := rfl
theorem cornerAt345_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 345 .east = false := rfl
theorem cornerAt345_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) 345 .west = false := rfl
end NetHack.Soko12Forward220.Unified.P05
