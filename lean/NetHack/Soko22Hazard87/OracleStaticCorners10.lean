import NetHack.Soko22Hazard87.OracleStaticCorners09
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem cornerAt250_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 250 .north = false := rfl
theorem cornerAt250_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 250 .south = false := rfl
theorem cornerAt250_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 250 .east = false := rfl
theorem cornerAt250_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 250 .west = false := rfl
theorem cornerAt250_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 250 .northEast = (true && p 251) := rfl
theorem cornerAt250_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 250 .northWest = (true && p 249) := rfl
theorem cornerAt250_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 250 .southEast = (true && p 251) := rfl
theorem cornerAt250_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 250 .southWest = (true && p 249) := rfl
theorem cornerAt251_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 251 .north = false := rfl
theorem cornerAt251_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 251 .south = false := rfl
theorem cornerAt251_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 251 .east = false := rfl
theorem cornerAt251_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 251 .west = false := rfl
theorem cornerAt251_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 251 .northEast = (true && p 252) := rfl
theorem cornerAt251_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 251 .northWest = (true && p 250) := rfl
theorem cornerAt251_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 251 .southEast = (true && p 252) := rfl
theorem cornerAt251_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 251 .southWest = (true && p 250) := rfl
theorem cornerAt252_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 252 .north = false := rfl
theorem cornerAt252_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 252 .south = false := rfl
theorem cornerAt252_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 252 .east = false := rfl
theorem cornerAt252_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 252 .west = false := rfl
theorem cornerAt252_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 252 .northEast = (true && p 253) := rfl
theorem cornerAt252_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 252 .northWest = (true && p 251) := rfl
theorem cornerAt252_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 252 .southEast = (true && p 253) := rfl
theorem cornerAt252_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 252 .southWest = (true && p 251) := rfl
theorem cornerAt253_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 253 .north = false := rfl
theorem cornerAt253_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 253 .south = false := rfl
theorem cornerAt253_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 253 .east = false := rfl
theorem cornerAt253_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 253 .west = false := rfl
theorem cornerAt253_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 253 .northEast = (true && p 254) := rfl
theorem cornerAt253_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 253 .northWest = (true && p 252) := rfl
theorem cornerAt253_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 253 .southEast = (true && p 254) := rfl
theorem cornerAt253_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 253 .southWest = (true && p 252) := rfl
theorem cornerAt254_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 254 .north = false := rfl
theorem cornerAt254_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 254 .south = false := rfl
theorem cornerAt254_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 254 .east = false := rfl
theorem cornerAt254_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 254 .west = false := rfl
theorem cornerAt254_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 254 .northEast = (true && p 255) := rfl
theorem cornerAt254_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 254 .northWest = (true && p 253) := rfl
theorem cornerAt254_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 254 .southEast = (true && p 255) := rfl
theorem cornerAt254_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 254 .southWest = (true && p 253) := rfl
theorem cornerAt255_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 255 .north = false := rfl
theorem cornerAt255_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 255 .south = false := rfl
theorem cornerAt255_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 255 .east = false := rfl
theorem cornerAt255_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 255 .west = false := rfl
theorem cornerAt255_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 255 .northEast = (true && p 256) := rfl
theorem cornerAt255_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 255 .northWest = (true && p 254) := rfl
theorem cornerAt255_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 255 .southEast = (true && p 256) := rfl
theorem cornerAt255_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 255 .southWest = (true && p 254) := rfl
theorem cornerAt256_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 256 .north = false := rfl
theorem cornerAt256_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 256 .south = false := rfl
theorem cornerAt256_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 256 .east = false := rfl
theorem cornerAt256_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 256 .west = false := rfl
theorem cornerAt256_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 256 .northEast = (true && p 257) := rfl
theorem cornerAt256_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 256 .northWest = (true && p 255) := rfl
theorem cornerAt256_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 256 .southEast = (true && p 257) := rfl
theorem cornerAt256_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 256 .southWest = (true && p 255) := rfl
theorem cornerAt257_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 257 .north = false := rfl
theorem cornerAt257_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 257 .south = false := rfl
theorem cornerAt257_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 257 .east = false := rfl
theorem cornerAt257_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 257 .west = false := rfl
theorem cornerAt257_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 257 .northEast = (true && p 258) := rfl
theorem cornerAt257_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 257 .northWest = (true && p 256) := rfl
theorem cornerAt257_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 257 .southEast = (true && p 258) := rfl
theorem cornerAt257_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 257 .southWest = (true && p 256) := rfl
theorem cornerAt258_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 258 .north = false := rfl
theorem cornerAt258_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 258 .south = false := rfl
theorem cornerAt258_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 258 .east = false := rfl
theorem cornerAt258_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 258 .west = false := rfl
theorem cornerAt258_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 258 .northEast = (true && p 259) := rfl
theorem cornerAt258_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 258 .northWest = (true && p 257) := rfl
theorem cornerAt258_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 258 .southEast = (true && p 259) := rfl
theorem cornerAt258_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 258 .southWest = (true && p 257) := rfl
theorem cornerAt259_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 259 .north = false := rfl
theorem cornerAt259_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 259 .south = false := rfl
theorem cornerAt259_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 259 .east = false := rfl
theorem cornerAt259_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 259 .west = false := rfl
theorem cornerAt259_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 259 .northEast = (true && p 260) := rfl
theorem cornerAt259_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 259 .northWest = (true && p 258) := rfl
theorem cornerAt259_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 259 .southEast = (true && p 260) := rfl
theorem cornerAt259_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 259 .southWest = (true && p 258) := rfl
theorem cornerAt260_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 260 .north = false := rfl
theorem cornerAt260_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 260 .south = false := rfl
theorem cornerAt260_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 260 .east = false := rfl
theorem cornerAt260_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 260 .west = false := rfl
theorem cornerAt260_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 260 .northEast = (true && false) := rfl
theorem cornerAt260_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 260 .northWest = (true && p 259) := rfl
theorem cornerAt260_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 260 .southEast = (true && false) := rfl
theorem cornerAt260_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 260 .southWest = (true && p 259) := rfl
theorem cornerAt262_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 262 .north = false := rfl
theorem cornerAt262_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 262 .south = false := rfl
theorem cornerAt262_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 262 .east = false := rfl
theorem cornerAt262_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 262 .west = false := rfl
theorem cornerAt262_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 262 .northEast = (false && true) := rfl
theorem cornerAt262_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 262 .northWest = (false && false) := rfl
theorem cornerAt262_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 262 .southEast = (true && true) := rfl
theorem cornerAt262_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 262 .southWest = (true && false) := rfl
end NetHack.Soko22Hazard87
