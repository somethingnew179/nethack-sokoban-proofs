import NetHack.Soko22Hazard87.OracleStaticCorners08
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem cornerAt215_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 215 .northEast = (false && false) := rfl
theorem cornerAt215_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 215 .northWest = (false && false) := rfl
theorem cornerAt215_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 215 .southEast = (true && false) := rfl
theorem cornerAt215_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 215 .southWest = (true && false) := rfl
theorem cornerAt216_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 216 .north = false := rfl
theorem cornerAt216_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 216 .south = false := rfl
theorem cornerAt216_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 216 .east = false := rfl
theorem cornerAt216_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 216 .west = false := rfl
theorem cornerAt216_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 216 .northEast = (false && false) := rfl
theorem cornerAt216_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 216 .northWest = (false && false) := rfl
theorem cornerAt216_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 216 .southEast = (true && false) := rfl
theorem cornerAt216_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 216 .southWest = (true && false) := rfl
theorem cornerAt218_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 218 .north = false := rfl
theorem cornerAt218_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 218 .south = false := rfl
theorem cornerAt218_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 218 .east = false := rfl
theorem cornerAt218_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 218 .west = false := rfl
theorem cornerAt218_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 218 .northEast = (true && true) := rfl
theorem cornerAt218_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 218 .northWest = (true && false) := rfl
theorem cornerAt218_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 218 .southEast = (false && true) := rfl
theorem cornerAt218_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 218 .southWest = (false && false) := rfl
theorem cornerAt223_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 223 .north = false := rfl
theorem cornerAt223_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 223 .south = false := rfl
theorem cornerAt223_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 223 .east = false := rfl
theorem cornerAt223_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 223 .west = false := rfl
theorem cornerAt223_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 223 .northEast = (p 201 && p 224) := rfl
theorem cornerAt223_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 223 .northWest = (p 201 && true) := rfl
theorem cornerAt223_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 223 .southEast = (p 245 && p 224) := rfl
theorem cornerAt223_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 223 .southWest = (p 245 && true) := rfl
theorem cornerAt224_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 224 .north = false := rfl
theorem cornerAt224_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 224 .south = false := rfl
theorem cornerAt224_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 224 .east = false := rfl
theorem cornerAt224_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 224 .west = false := rfl
theorem cornerAt224_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 224 .northEast = (p 202 && p 225) := rfl
theorem cornerAt224_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 224 .northWest = (p 202 && p 223) := rfl
theorem cornerAt224_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 224 .southEast = (p 246 && p 225) := rfl
theorem cornerAt224_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 224 .southWest = (p 246 && p 223) := rfl
theorem cornerAt225_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 225 .north = false := rfl
theorem cornerAt225_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 225 .south = false := rfl
theorem cornerAt225_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 225 .east = false := rfl
theorem cornerAt225_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 225 .west = false := rfl
theorem cornerAt225_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 225 .northEast = (true && p 226) := rfl
theorem cornerAt225_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 225 .northWest = (true && p 224) := rfl
theorem cornerAt225_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 225 .southEast = (p 247 && p 226) := rfl
theorem cornerAt225_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 225 .southWest = (p 247 && p 224) := rfl
theorem cornerAt226_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 226 .north = false := rfl
theorem cornerAt226_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 226 .south = false := rfl
theorem cornerAt226_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 226 .east = false := rfl
theorem cornerAt226_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 226 .west = false := rfl
theorem cornerAt226_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 226 .northEast = (p 204 && true) := rfl
theorem cornerAt226_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 226 .northWest = (p 204 && p 225) := rfl
theorem cornerAt226_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 226 .southEast = (p 248 && true) := rfl
theorem cornerAt226_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 226 .southWest = (p 248 && p 225) := rfl
theorem cornerAt240_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 240 .north = false := rfl
theorem cornerAt240_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 240 .south = false := rfl
theorem cornerAt240_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 240 .east = false := rfl
theorem cornerAt240_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 240 .west = false := rfl
theorem cornerAt240_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 240 .northEast = (false && true) := rfl
theorem cornerAt240_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 240 .northWest = (false && true) := rfl
theorem cornerAt240_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 240 .southEast = (false && true) := rfl
theorem cornerAt240_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 240 .southWest = (false && true) := rfl
theorem cornerAt245_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 245 .north = false := rfl
theorem cornerAt245_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 245 .south = false := rfl
theorem cornerAt245_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 245 .east = false := rfl
theorem cornerAt245_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 245 .west = false := rfl
theorem cornerAt245_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 245 .northEast = (p 223 && p 246) := rfl
theorem cornerAt245_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 245 .northWest = (p 223 && true) := rfl
theorem cornerAt245_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 245 .southEast = (true && p 246) := rfl
theorem cornerAt245_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 245 .southWest = (true && true) := rfl
theorem cornerAt246_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 246 .north = false := rfl
theorem cornerAt246_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 246 .south = false := rfl
theorem cornerAt246_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 246 .east = false := rfl
theorem cornerAt246_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 246 .west = false := rfl
theorem cornerAt246_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 246 .northEast = (p 224 && p 247) := rfl
theorem cornerAt246_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 246 .northWest = (p 224 && p 245) := rfl
theorem cornerAt246_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 246 .southEast = (true && p 247) := rfl
theorem cornerAt246_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 246 .southWest = (true && p 245) := rfl
theorem cornerAt247_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 247 .north = false := rfl
theorem cornerAt247_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 247 .south = false := rfl
theorem cornerAt247_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 247 .east = false := rfl
theorem cornerAt247_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 247 .west = false := rfl
theorem cornerAt247_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 247 .northEast = (p 225 && p 248) := rfl
theorem cornerAt247_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 247 .northWest = (p 225 && p 246) := rfl
theorem cornerAt247_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 247 .southEast = (true && p 248) := rfl
theorem cornerAt247_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 247 .southWest = (true && p 246) := rfl
theorem cornerAt248_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 248 .north = false := rfl
theorem cornerAt248_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 248 .south = false := rfl
theorem cornerAt248_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 248 .east = false := rfl
theorem cornerAt248_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 248 .west = false := rfl
theorem cornerAt248_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 248 .northEast = (p 226 && p 249) := rfl
theorem cornerAt248_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 248 .northWest = (p 226 && p 247) := rfl
theorem cornerAt248_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 248 .southEast = (true && p 249) := rfl
theorem cornerAt248_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 248 .southWest = (true && p 247) := rfl
theorem cornerAt249_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 249 .north = false := rfl
theorem cornerAt249_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 249 .south = false := rfl
theorem cornerAt249_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 249 .east = false := rfl
theorem cornerAt249_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 249 .west = false := rfl
theorem cornerAt249_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 249 .northEast = (true && p 250) := rfl
theorem cornerAt249_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 249 .northWest = (true && p 248) := rfl
theorem cornerAt249_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 249 .southEast = (true && p 250) := rfl
theorem cornerAt249_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 249 .southWest = (true && p 248) := rfl
end NetHack.Soko22Hazard87
