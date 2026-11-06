import NetHack.Soko12Forward220.Unified.P04.OracleCells05
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P04
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem floorAt240 : soko1_2.board.floor.contains 240 = false := by decide +kernel
theorem doorAt240 : soko1_2.board.doors.contains 240 = false := by decide +kernel
theorem trapAt240 : soko1_2.board.rollingTraps.contains 240 = false := by decide +kernel
theorem boxAt240 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 240 = false := rfl
theorem holeAt240 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 240 = false := rfl
theorem advanceAt240_north : advance soko1_2.board 240 .north = some 214 := by decide +kernel
theorem advanceAt240_south : advance soko1_2.board 240 .south = some 266 := by decide +kernel
theorem advanceAt240_east : advance soko1_2.board 240 .east = some 241 := by decide +kernel
theorem advanceAt240_west : advance soko1_2.board 240 .west = some 239 := by decide +kernel
theorem advanceAt240_northEast : advance soko1_2.board 240 .northEast = some 215 := by decide +kernel
theorem advanceAt240_northWest : advance soko1_2.board 240 .northWest = some 213 := by decide +kernel
theorem advanceAt240_southEast : advance soko1_2.board 240 .southEast = some 267 := by decide +kernel
theorem advanceAt240_southWest : advance soko1_2.board 240 .southWest = some 265 := by decide +kernel
theorem floorAt241 : soko1_2.board.floor.contains 241 = true := by decide +kernel
theorem doorAt241 : soko1_2.board.doors.contains 241 = false := by decide +kernel
theorem trapAt241 : soko1_2.board.rollingTraps.contains 241 = false := by decide +kernel
theorem boxAt241 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 241 = p 241 := rfl
theorem holeAt241 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 241 = false := rfl
theorem advanceAt241_north : advance soko1_2.board 241 .north = some 215 := by decide +kernel
theorem advanceAt241_south : advance soko1_2.board 241 .south = some 267 := by decide +kernel
theorem advanceAt241_east : advance soko1_2.board 241 .east = some 242 := by decide +kernel
theorem advanceAt241_west : advance soko1_2.board 241 .west = some 240 := by decide +kernel
theorem advanceAt241_northEast : advance soko1_2.board 241 .northEast = some 216 := by decide +kernel
theorem advanceAt241_northWest : advance soko1_2.board 241 .northWest = some 214 := by decide +kernel
theorem advanceAt241_southEast : advance soko1_2.board 241 .southEast = some 268 := by decide +kernel
theorem advanceAt241_southWest : advance soko1_2.board 241 .southWest = some 266 := by decide +kernel
theorem floorAt242 : soko1_2.board.floor.contains 242 = true := by decide +kernel
theorem doorAt242 : soko1_2.board.doors.contains 242 = false := by decide +kernel
theorem trapAt242 : soko1_2.board.rollingTraps.contains 242 = false := by decide +kernel
theorem boxAt242 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 242 = p 242 := rfl
theorem holeAt242 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 242 = false := rfl
theorem advanceAt242_north : advance soko1_2.board 242 .north = some 216 := by decide +kernel
theorem advanceAt242_south : advance soko1_2.board 242 .south = some 268 := by decide +kernel
theorem advanceAt242_east : advance soko1_2.board 242 .east = some 243 := by decide +kernel
theorem advanceAt242_west : advance soko1_2.board 242 .west = some 241 := by decide +kernel
theorem advanceAt242_northEast : advance soko1_2.board 242 .northEast = some 217 := by decide +kernel
theorem advanceAt242_northWest : advance soko1_2.board 242 .northWest = some 215 := by decide +kernel
theorem advanceAt242_southEast : advance soko1_2.board 242 .southEast = some 269 := by decide +kernel
theorem advanceAt242_southWest : advance soko1_2.board 242 .southWest = some 267 := by decide +kernel
theorem floorAt243 : soko1_2.board.floor.contains 243 = false := by decide +kernel
theorem doorAt243 : soko1_2.board.doors.contains 243 = false := by decide +kernel
theorem trapAt243 : soko1_2.board.rollingTraps.contains 243 = false := by decide +kernel
theorem boxAt243 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 243 = false := rfl
theorem holeAt243 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 243 = false := rfl
theorem advanceAt243_north : advance soko1_2.board 243 .north = some 217 := by decide +kernel
theorem advanceAt243_south : advance soko1_2.board 243 .south = some 269 := by decide +kernel
theorem advanceAt243_east : advance soko1_2.board 243 .east = some 244 := by decide +kernel
theorem advanceAt243_west : advance soko1_2.board 243 .west = some 242 := by decide +kernel
theorem advanceAt243_northEast : advance soko1_2.board 243 .northEast = some 218 := by decide +kernel
theorem advanceAt243_northWest : advance soko1_2.board 243 .northWest = some 216 := by decide +kernel
theorem advanceAt243_southEast : advance soko1_2.board 243 .southEast = some 270 := by decide +kernel
theorem advanceAt243_southWest : advance soko1_2.board 243 .southWest = some 268 := by decide +kernel
theorem floorAt244 : soko1_2.board.floor.contains 244 = true := by decide +kernel
theorem doorAt244 : soko1_2.board.doors.contains 244 = false := by decide +kernel
theorem trapAt244 : soko1_2.board.rollingTraps.contains 244 = false := by decide +kernel
theorem boxAt244 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 244 = p 244 := rfl
theorem holeAt244 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 244 = false := rfl
theorem advanceAt244_north : advance soko1_2.board 244 .north = some 218 := by decide +kernel
theorem advanceAt244_south : advance soko1_2.board 244 .south = some 270 := by decide +kernel
theorem advanceAt244_east : advance soko1_2.board 244 .east = some 245 := by decide +kernel
theorem advanceAt244_west : advance soko1_2.board 244 .west = some 243 := by decide +kernel
theorem advanceAt244_northEast : advance soko1_2.board 244 .northEast = some 219 := by decide +kernel
theorem advanceAt244_northWest : advance soko1_2.board 244 .northWest = some 217 := by decide +kernel
theorem advanceAt244_southEast : advance soko1_2.board 244 .southEast = some 271 := by decide +kernel
theorem advanceAt244_southWest : advance soko1_2.board 244 .southWest = some 269 := by decide +kernel
theorem floorAt245 : soko1_2.board.floor.contains 245 = true := by decide +kernel
theorem doorAt245 : soko1_2.board.doors.contains 245 = false := by decide +kernel
theorem trapAt245 : soko1_2.board.rollingTraps.contains 245 = false := by decide +kernel
theorem boxAt245 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 245 = p 245 := rfl
theorem holeAt245 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 245 = false := rfl
theorem advanceAt245_north : advance soko1_2.board 245 .north = some 219 := by decide +kernel
theorem advanceAt245_south : advance soko1_2.board 245 .south = some 271 := by decide +kernel
theorem advanceAt245_east : advance soko1_2.board 245 .east = some 246 := by decide +kernel
theorem advanceAt245_west : advance soko1_2.board 245 .west = some 244 := by decide +kernel
theorem advanceAt245_northEast : advance soko1_2.board 245 .northEast = some 220 := by decide +kernel
theorem advanceAt245_northWest : advance soko1_2.board 245 .northWest = some 218 := by decide +kernel
theorem advanceAt245_southEast : advance soko1_2.board 245 .southEast = some 272 := by decide +kernel
theorem advanceAt245_southWest : advance soko1_2.board 245 .southWest = some 270 := by decide +kernel
theorem floorAt246 : soko1_2.board.floor.contains 246 = true := by decide +kernel
theorem doorAt246 : soko1_2.board.doors.contains 246 = false := by decide +kernel
theorem trapAt246 : soko1_2.board.rollingTraps.contains 246 = false := by decide +kernel
theorem boxAt246 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 246 = p 246 := rfl
theorem holeAt246 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 246 = false := rfl
theorem advanceAt246_north : advance soko1_2.board 246 .north = some 220 := by decide +kernel
theorem advanceAt246_south : advance soko1_2.board 246 .south = some 272 := by decide +kernel
theorem advanceAt246_east : advance soko1_2.board 246 .east = some 247 := by decide +kernel
theorem advanceAt246_west : advance soko1_2.board 246 .west = some 245 := by decide +kernel
theorem advanceAt246_northEast : advance soko1_2.board 246 .northEast = some 221 := by decide +kernel
theorem advanceAt246_northWest : advance soko1_2.board 246 .northWest = some 219 := by decide +kernel
theorem advanceAt246_southEast : advance soko1_2.board 246 .southEast = some 273 := by decide +kernel
theorem advanceAt246_southWest : advance soko1_2.board 246 .southWest = some 271 := by decide +kernel
theorem floorAt247 : soko1_2.board.floor.contains 247 = false := by decide +kernel
theorem doorAt247 : soko1_2.board.doors.contains 247 = false := by decide +kernel
theorem trapAt247 : soko1_2.board.rollingTraps.contains 247 = false := by decide +kernel
theorem boxAt247 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 247 = false := rfl
theorem holeAt247 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 247 = false := rfl
theorem advanceAt247_north : advance soko1_2.board 247 .north = some 221 := by decide +kernel
theorem advanceAt247_south : advance soko1_2.board 247 .south = some 273 := by decide +kernel
theorem advanceAt247_east : advance soko1_2.board 247 .east = some 248 := by decide +kernel
theorem advanceAt247_west : advance soko1_2.board 247 .west = some 246 := by decide +kernel
theorem advanceAt247_northEast : advance soko1_2.board 247 .northEast = some 222 := by decide +kernel
theorem advanceAt247_northWest : advance soko1_2.board 247 .northWest = some 220 := by decide +kernel
theorem advanceAt247_southEast : advance soko1_2.board 247 .southEast = some 274 := by decide +kernel
theorem advanceAt247_southWest : advance soko1_2.board 247 .southWest = some 272 := by decide +kernel
theorem floorAt248 : soko1_2.board.floor.contains 248 = false := by decide +kernel
theorem doorAt248 : soko1_2.board.doors.contains 248 = false := by decide +kernel
theorem trapAt248 : soko1_2.board.rollingTraps.contains 248 = false := by decide +kernel
theorem boxAt248 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 248 = false := rfl
theorem holeAt248 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 248 = false := rfl
theorem advanceAt248_north : advance soko1_2.board 248 .north = some 222 := by decide +kernel
theorem advanceAt248_south : advance soko1_2.board 248 .south = some 274 := by decide +kernel
theorem advanceAt248_east : advance soko1_2.board 248 .east = some 249 := by decide +kernel
theorem advanceAt248_west : advance soko1_2.board 248 .west = some 247 := by decide +kernel
theorem advanceAt248_northEast : advance soko1_2.board 248 .northEast = some 223 := by decide +kernel
theorem advanceAt248_northWest : advance soko1_2.board 248 .northWest = some 221 := by decide +kernel
theorem advanceAt248_southEast : advance soko1_2.board 248 .southEast = some 275 := by decide +kernel
theorem advanceAt248_southWest : advance soko1_2.board 248 .southWest = some 273 := by decide +kernel
theorem floorAt249 : soko1_2.board.floor.contains 249 = false := by decide +kernel
theorem doorAt249 : soko1_2.board.doors.contains 249 = false := by decide +kernel
theorem trapAt249 : soko1_2.board.rollingTraps.contains 249 = false := by decide +kernel
theorem boxAt249 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 249 = false := rfl
theorem holeAt249 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 249 = false := rfl
theorem advanceAt249_north : advance soko1_2.board 249 .north = some 223 := by decide +kernel
theorem advanceAt249_south : advance soko1_2.board 249 .south = some 275 := by decide +kernel
theorem advanceAt249_east : advance soko1_2.board 249 .east = some 250 := by decide +kernel
theorem advanceAt249_west : advance soko1_2.board 249 .west = some 248 := by decide +kernel
theorem advanceAt249_northEast : advance soko1_2.board 249 .northEast = some 224 := by decide +kernel
theorem advanceAt249_northWest : advance soko1_2.board 249 .northWest = some 222 := by decide +kernel
theorem advanceAt249_southEast : advance soko1_2.board 249 .southEast = some 276 := by decide +kernel
theorem advanceAt249_southWest : advance soko1_2.board 249 .southWest = some 274 := by decide +kernel
theorem floorAt250 : soko1_2.board.floor.contains 250 = false := by decide +kernel
theorem doorAt250 : soko1_2.board.doors.contains 250 = false := by decide +kernel
theorem trapAt250 : soko1_2.board.rollingTraps.contains 250 = false := by decide +kernel
theorem boxAt250 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 250 = false := rfl
theorem holeAt250 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 250 = false := rfl
theorem advanceAt250_north : advance soko1_2.board 250 .north = some 224 := by decide +kernel
theorem advanceAt250_south : advance soko1_2.board 250 .south = some 276 := by decide +kernel
theorem advanceAt250_east : advance soko1_2.board 250 .east = some 251 := by decide +kernel
theorem advanceAt250_west : advance soko1_2.board 250 .west = some 249 := by decide +kernel
theorem advanceAt250_northEast : advance soko1_2.board 250 .northEast = some 225 := by decide +kernel
theorem advanceAt250_northWest : advance soko1_2.board 250 .northWest = some 223 := by decide +kernel
theorem advanceAt250_southEast : advance soko1_2.board 250 .southEast = some 277 := by decide +kernel
theorem advanceAt250_southWest : advance soko1_2.board 250 .southWest = some 275 := by decide +kernel
theorem floorAt251 : soko1_2.board.floor.contains 251 = false := by decide +kernel
theorem doorAt251 : soko1_2.board.doors.contains 251 = false := by decide +kernel
theorem trapAt251 : soko1_2.board.rollingTraps.contains 251 = false := by decide +kernel
theorem boxAt251 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 251 = false := rfl
theorem holeAt251 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 251 = false := rfl
theorem advanceAt251_north : advance soko1_2.board 251 .north = some 225 := by decide +kernel
theorem advanceAt251_south : advance soko1_2.board 251 .south = some 277 := by decide +kernel
theorem advanceAt251_east : advance soko1_2.board 251 .east = some 252 := by decide +kernel
theorem advanceAt251_west : advance soko1_2.board 251 .west = some 250 := by decide +kernel
theorem advanceAt251_northEast : advance soko1_2.board 251 .northEast = some 226 := by decide +kernel
theorem advanceAt251_northWest : advance soko1_2.board 251 .northWest = some 224 := by decide +kernel
theorem advanceAt251_southEast : advance soko1_2.board 251 .southEast = some 278 := by decide +kernel
theorem advanceAt251_southWest : advance soko1_2.board 251 .southWest = some 276 := by decide +kernel
theorem floorAt252 : soko1_2.board.floor.contains 252 = true := by decide +kernel
theorem doorAt252 : soko1_2.board.doors.contains 252 = false := by decide +kernel
theorem trapAt252 : soko1_2.board.rollingTraps.contains 252 = false := by decide +kernel
theorem boxAt252 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 252 = false := rfl
theorem holeAt252 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 252 = false := rfl
theorem advanceAt252_north : advance soko1_2.board 252 .north = some 226 := by decide +kernel
theorem advanceAt252_south : advance soko1_2.board 252 .south = some 278 := by decide +kernel
theorem advanceAt252_east : advance soko1_2.board 252 .east = some 253 := by decide +kernel
theorem advanceAt252_west : advance soko1_2.board 252 .west = some 251 := by decide +kernel
theorem advanceAt252_northEast : advance soko1_2.board 252 .northEast = some 227 := by decide +kernel
theorem advanceAt252_northWest : advance soko1_2.board 252 .northWest = some 225 := by decide +kernel
theorem advanceAt252_southEast : advance soko1_2.board 252 .southEast = some 279 := by decide +kernel
theorem advanceAt252_southWest : advance soko1_2.board 252 .southWest = some 277 := by decide +kernel
theorem floorAt253 : soko1_2.board.floor.contains 253 = true := by decide +kernel
theorem doorAt253 : soko1_2.board.doors.contains 253 = false := by decide +kernel
theorem trapAt253 : soko1_2.board.rollingTraps.contains 253 = false := by decide +kernel
theorem boxAt253 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 253 = false := rfl
theorem holeAt253 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 253 = false := rfl
theorem advanceAt253_north : advance soko1_2.board 253 .north = some 227 := by decide +kernel
theorem advanceAt253_south : advance soko1_2.board 253 .south = some 279 := by decide +kernel
theorem advanceAt253_east : advance soko1_2.board 253 .east = some 254 := by decide +kernel
theorem advanceAt253_west : advance soko1_2.board 253 .west = some 252 := by decide +kernel
theorem advanceAt253_northEast : advance soko1_2.board 253 .northEast = some 228 := by decide +kernel
theorem advanceAt253_northWest : advance soko1_2.board 253 .northWest = some 226 := by decide +kernel
theorem advanceAt253_southEast : advance soko1_2.board 253 .southEast = some 280 := by decide +kernel
theorem advanceAt253_southWest : advance soko1_2.board 253 .southWest = some 278 := by decide +kernel
theorem floorAt254 : soko1_2.board.floor.contains 254 = true := by decide +kernel
theorem doorAt254 : soko1_2.board.doors.contains 254 = false := by decide +kernel
theorem trapAt254 : soko1_2.board.rollingTraps.contains 254 = false := by decide +kernel
theorem boxAt254 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 254 = false := rfl
theorem holeAt254 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 254 = false := rfl
theorem advanceAt254_north : advance soko1_2.board 254 .north = some 228 := by decide +kernel
theorem advanceAt254_south : advance soko1_2.board 254 .south = some 280 := by decide +kernel
theorem advanceAt254_east : advance soko1_2.board 254 .east = some 255 := by decide +kernel
theorem advanceAt254_west : advance soko1_2.board 254 .west = some 253 := by decide +kernel
theorem advanceAt254_northEast : advance soko1_2.board 254 .northEast = some 229 := by decide +kernel
theorem advanceAt254_northWest : advance soko1_2.board 254 .northWest = some 227 := by decide +kernel
theorem advanceAt254_southEast : advance soko1_2.board 254 .southEast = some 281 := by decide +kernel
theorem advanceAt254_southWest : advance soko1_2.board 254 .southWest = some 279 := by decide +kernel
theorem floorAt255 : soko1_2.board.floor.contains 255 = true := by decide +kernel
theorem doorAt255 : soko1_2.board.doors.contains 255 = false := by decide +kernel
theorem trapAt255 : soko1_2.board.rollingTraps.contains 255 = false := by decide +kernel
theorem boxAt255 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 255 = false := rfl
theorem holeAt255 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 255 = false := rfl
theorem advanceAt255_north : advance soko1_2.board 255 .north = some 229 := by decide +kernel
theorem advanceAt255_south : advance soko1_2.board 255 .south = some 281 := by decide +kernel
theorem advanceAt255_east : advance soko1_2.board 255 .east = some 256 := by decide +kernel
theorem advanceAt255_west : advance soko1_2.board 255 .west = some 254 := by decide +kernel
theorem advanceAt255_northEast : advance soko1_2.board 255 .northEast = some 230 := by decide +kernel
theorem advanceAt255_northWest : advance soko1_2.board 255 .northWest = some 228 := by decide +kernel
theorem advanceAt255_southEast : advance soko1_2.board 255 .southEast = some 282 := by decide +kernel
theorem advanceAt255_southWest : advance soko1_2.board 255 .southWest = some 280 := by decide +kernel
theorem floorAt256 : soko1_2.board.floor.contains 256 = true := by decide +kernel
theorem doorAt256 : soko1_2.board.doors.contains 256 = false := by decide +kernel
theorem trapAt256 : soko1_2.board.rollingTraps.contains 256 = false := by decide +kernel
theorem boxAt256 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 256 = false := rfl
theorem holeAt256 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 256 = false := rfl
theorem advanceAt256_north : advance soko1_2.board 256 .north = some 230 := by decide +kernel
theorem advanceAt256_south : advance soko1_2.board 256 .south = some 282 := by decide +kernel
theorem advanceAt256_east : advance soko1_2.board 256 .east = some 257 := by decide +kernel
theorem advanceAt256_west : advance soko1_2.board 256 .west = some 255 := by decide +kernel
theorem advanceAt256_northEast : advance soko1_2.board 256 .northEast = some 231 := by decide +kernel
theorem advanceAt256_northWest : advance soko1_2.board 256 .northWest = some 229 := by decide +kernel
theorem advanceAt256_southEast : advance soko1_2.board 256 .southEast = some 283 := by decide +kernel
theorem advanceAt256_southWest : advance soko1_2.board 256 .southWest = some 281 := by decide +kernel
theorem floorAt257 : soko1_2.board.floor.contains 257 = false := by decide +kernel
theorem doorAt257 : soko1_2.board.doors.contains 257 = false := by decide +kernel
theorem trapAt257 : soko1_2.board.rollingTraps.contains 257 = false := by decide +kernel
theorem boxAt257 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 257 = false := rfl
theorem holeAt257 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 257 = false := rfl
theorem advanceAt257_north : advance soko1_2.board 257 .north = some 231 := by decide +kernel
theorem advanceAt257_south : advance soko1_2.board 257 .south = some 283 := by decide +kernel
theorem advanceAt257_east : advance soko1_2.board 257 .east = some 258 := by decide +kernel
theorem advanceAt257_west : advance soko1_2.board 257 .west = some 256 := by decide +kernel
theorem advanceAt257_northEast : advance soko1_2.board 257 .northEast = some 232 := by decide +kernel
theorem advanceAt257_northWest : advance soko1_2.board 257 .northWest = some 230 := by decide +kernel
theorem advanceAt257_southEast : advance soko1_2.board 257 .southEast = some 284 := by decide +kernel
theorem advanceAt257_southWest : advance soko1_2.board 257 .southWest = some 282 := by decide +kernel
theorem floorAt258 : soko1_2.board.floor.contains 258 = true := by decide +kernel
theorem doorAt258 : soko1_2.board.doors.contains 258 = false := by decide +kernel
theorem trapAt258 : soko1_2.board.rollingTraps.contains 258 = false := by decide +kernel
theorem boxAt258 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 258 = false := rfl
theorem holeAt258 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 258 = false := rfl
theorem advanceAt258_north : advance soko1_2.board 258 .north = some 232 := by decide +kernel
theorem advanceAt258_south : advance soko1_2.board 258 .south = some 284 := by decide +kernel
theorem advanceAt258_east : advance soko1_2.board 258 .east = some 259 := by decide +kernel
theorem advanceAt258_west : advance soko1_2.board 258 .west = some 257 := by decide +kernel
theorem advanceAt258_northEast : advance soko1_2.board 258 .northEast = some 233 := by decide +kernel
theorem advanceAt258_northWest : advance soko1_2.board 258 .northWest = some 231 := by decide +kernel
theorem advanceAt258_southEast : advance soko1_2.board 258 .southEast = some 285 := by decide +kernel
theorem advanceAt258_southWest : advance soko1_2.board 258 .southWest = some 283 := by decide +kernel
theorem floorAt259 : soko1_2.board.floor.contains 259 = false := by decide +kernel
theorem doorAt259 : soko1_2.board.doors.contains 259 = false := by decide +kernel
theorem trapAt259 : soko1_2.board.rollingTraps.contains 259 = false := by decide +kernel
theorem boxAt259 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 259 = false := rfl
theorem holeAt259 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 259 = false := rfl
theorem advanceAt259_north : advance soko1_2.board 259 .north = some 233 := by decide +kernel
theorem advanceAt259_south : advance soko1_2.board 259 .south = some 285 := by decide +kernel
theorem advanceAt259_east : advance soko1_2.board 259 .east = none := by decide +kernel
theorem advanceAt259_west : advance soko1_2.board 259 .west = some 258 := by decide +kernel
theorem advanceAt259_northEast : advance soko1_2.board 259 .northEast = none := by decide +kernel
theorem advanceAt259_northWest : advance soko1_2.board 259 .northWest = some 232 := by decide +kernel
theorem advanceAt259_southEast : advance soko1_2.board 259 .southEast = none := by decide +kernel
theorem advanceAt259_southWest : advance soko1_2.board 259 .southWest = some 284 := by decide +kernel
theorem floorAt260 : soko1_2.board.floor.contains 260 = false := by decide +kernel
theorem doorAt260 : soko1_2.board.doors.contains 260 = false := by decide +kernel
theorem trapAt260 : soko1_2.board.rollingTraps.contains 260 = false := by decide +kernel
theorem boxAt260 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 260 = false := rfl
theorem holeAt260 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 260 = false := rfl
theorem advanceAt260_north : advance soko1_2.board 260 .north = some 234 := by decide +kernel
theorem advanceAt260_south : advance soko1_2.board 260 .south = some 286 := by decide +kernel
theorem advanceAt260_east : advance soko1_2.board 260 .east = some 261 := by decide +kernel
theorem advanceAt260_west : advance soko1_2.board 260 .west = none := by decide +kernel
theorem advanceAt260_northEast : advance soko1_2.board 260 .northEast = some 235 := by decide +kernel
theorem advanceAt260_northWest : advance soko1_2.board 260 .northWest = none := by decide +kernel
theorem advanceAt260_southEast : advance soko1_2.board 260 .southEast = some 287 := by decide +kernel
theorem advanceAt260_southWest : advance soko1_2.board 260 .southWest = none := by decide +kernel
theorem floorAt261 : soko1_2.board.floor.contains 261 = false := by decide +kernel
theorem doorAt261 : soko1_2.board.doors.contains 261 = false := by decide +kernel
theorem trapAt261 : soko1_2.board.rollingTraps.contains 261 = false := by decide +kernel
theorem boxAt261 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 261 = false := rfl
theorem holeAt261 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 261 = false := rfl
theorem advanceAt261_north : advance soko1_2.board 261 .north = some 235 := by decide +kernel
theorem advanceAt261_south : advance soko1_2.board 261 .south = some 287 := by decide +kernel
theorem advanceAt261_east : advance soko1_2.board 261 .east = some 262 := by decide +kernel
theorem advanceAt261_west : advance soko1_2.board 261 .west = some 260 := by decide +kernel
theorem advanceAt261_northEast : advance soko1_2.board 261 .northEast = some 236 := by decide +kernel
theorem advanceAt261_northWest : advance soko1_2.board 261 .northWest = some 234 := by decide +kernel
theorem advanceAt261_southEast : advance soko1_2.board 261 .southEast = some 288 := by decide +kernel
theorem advanceAt261_southWest : advance soko1_2.board 261 .southWest = some 286 := by decide +kernel
theorem floorAt262 : soko1_2.board.floor.contains 262 = true := by decide +kernel
theorem doorAt262 : soko1_2.board.doors.contains 262 = false := by decide +kernel
theorem trapAt262 : soko1_2.board.rollingTraps.contains 262 = false := by decide +kernel
theorem boxAt262 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 262 = p 262 := rfl
theorem holeAt262 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 262 = false := rfl
theorem advanceAt262_north : advance soko1_2.board 262 .north = some 236 := by decide +kernel
theorem advanceAt262_south : advance soko1_2.board 262 .south = some 288 := by decide +kernel
theorem advanceAt262_east : advance soko1_2.board 262 .east = some 263 := by decide +kernel
theorem advanceAt262_west : advance soko1_2.board 262 .west = some 261 := by decide +kernel
theorem advanceAt262_northEast : advance soko1_2.board 262 .northEast = some 237 := by decide +kernel
theorem advanceAt262_northWest : advance soko1_2.board 262 .northWest = some 235 := by decide +kernel
theorem advanceAt262_southEast : advance soko1_2.board 262 .southEast = some 289 := by decide +kernel
theorem advanceAt262_southWest : advance soko1_2.board 262 .southWest = some 287 := by decide +kernel
theorem floorAt263 : soko1_2.board.floor.contains 263 = true := by decide +kernel
theorem doorAt263 : soko1_2.board.doors.contains 263 = false := by decide +kernel
theorem trapAt263 : soko1_2.board.rollingTraps.contains 263 = false := by decide +kernel
theorem boxAt263 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 263 = p 263 := rfl
theorem holeAt263 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 263 = false := rfl
theorem advanceAt263_north : advance soko1_2.board 263 .north = some 237 := by decide +kernel
theorem advanceAt263_south : advance soko1_2.board 263 .south = some 289 := by decide +kernel
theorem advanceAt263_east : advance soko1_2.board 263 .east = some 264 := by decide +kernel
theorem advanceAt263_west : advance soko1_2.board 263 .west = some 262 := by decide +kernel
theorem advanceAt263_northEast : advance soko1_2.board 263 .northEast = some 238 := by decide +kernel
theorem advanceAt263_northWest : advance soko1_2.board 263 .northWest = some 236 := by decide +kernel
theorem advanceAt263_southEast : advance soko1_2.board 263 .southEast = some 290 := by decide +kernel
theorem advanceAt263_southWest : advance soko1_2.board 263 .southWest = some 288 := by decide +kernel
theorem floorAt264 : soko1_2.board.floor.contains 264 = true := by decide +kernel
theorem doorAt264 : soko1_2.board.doors.contains 264 = false := by decide +kernel
theorem trapAt264 : soko1_2.board.rollingTraps.contains 264 = false := by decide +kernel
theorem boxAt264 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 264 = p 264 := rfl
theorem holeAt264 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 264 = false := rfl
theorem advanceAt264_north : advance soko1_2.board 264 .north = some 238 := by decide +kernel
theorem advanceAt264_south : advance soko1_2.board 264 .south = some 290 := by decide +kernel
theorem advanceAt264_east : advance soko1_2.board 264 .east = some 265 := by decide +kernel
theorem advanceAt264_west : advance soko1_2.board 264 .west = some 263 := by decide +kernel
theorem advanceAt264_northEast : advance soko1_2.board 264 .northEast = some 239 := by decide +kernel
theorem advanceAt264_northWest : advance soko1_2.board 264 .northWest = some 237 := by decide +kernel
theorem advanceAt264_southEast : advance soko1_2.board 264 .southEast = some 291 := by decide +kernel
theorem advanceAt264_southWest : advance soko1_2.board 264 .southWest = some 289 := by decide +kernel
theorem floorAt265 : soko1_2.board.floor.contains 265 = true := by decide +kernel
theorem doorAt265 : soko1_2.board.doors.contains 265 = false := by decide +kernel
theorem trapAt265 : soko1_2.board.rollingTraps.contains 265 = false := by decide +kernel
theorem boxAt265 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 265 = p 265 := rfl
theorem holeAt265 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 265 = false := rfl
theorem advanceAt265_north : advance soko1_2.board 265 .north = some 239 := by decide +kernel
theorem advanceAt265_south : advance soko1_2.board 265 .south = some 291 := by decide +kernel
theorem advanceAt265_east : advance soko1_2.board 265 .east = some 266 := by decide +kernel
theorem advanceAt265_west : advance soko1_2.board 265 .west = some 264 := by decide +kernel
theorem advanceAt265_northEast : advance soko1_2.board 265 .northEast = some 240 := by decide +kernel
theorem advanceAt265_northWest : advance soko1_2.board 265 .northWest = some 238 := by decide +kernel
theorem advanceAt265_southEast : advance soko1_2.board 265 .southEast = some 292 := by decide +kernel
theorem advanceAt265_southWest : advance soko1_2.board 265 .southWest = some 290 := by decide +kernel
theorem floorAt266 : soko1_2.board.floor.contains 266 = false := by decide +kernel
theorem doorAt266 : soko1_2.board.doors.contains 266 = false := by decide +kernel
theorem trapAt266 : soko1_2.board.rollingTraps.contains 266 = false := by decide +kernel
theorem boxAt266 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 266 = false := rfl
theorem holeAt266 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 266 = false := rfl
theorem advanceAt266_north : advance soko1_2.board 266 .north = some 240 := by decide +kernel
theorem advanceAt266_south : advance soko1_2.board 266 .south = some 292 := by decide +kernel
theorem advanceAt266_east : advance soko1_2.board 266 .east = some 267 := by decide +kernel
theorem advanceAt266_west : advance soko1_2.board 266 .west = some 265 := by decide +kernel
theorem advanceAt266_northEast : advance soko1_2.board 266 .northEast = some 241 := by decide +kernel
theorem advanceAt266_northWest : advance soko1_2.board 266 .northWest = some 239 := by decide +kernel
theorem advanceAt266_southEast : advance soko1_2.board 266 .southEast = some 293 := by decide +kernel
theorem advanceAt266_southWest : advance soko1_2.board 266 .southWest = some 291 := by decide +kernel
theorem floorAt267 : soko1_2.board.floor.contains 267 = false := by decide +kernel
theorem doorAt267 : soko1_2.board.doors.contains 267 = false := by decide +kernel
theorem trapAt267 : soko1_2.board.rollingTraps.contains 267 = false := by decide +kernel
theorem boxAt267 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 267 = false := rfl
theorem holeAt267 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 267 = false := rfl
theorem advanceAt267_north : advance soko1_2.board 267 .north = some 241 := by decide +kernel
theorem advanceAt267_south : advance soko1_2.board 267 .south = some 293 := by decide +kernel
theorem advanceAt267_east : advance soko1_2.board 267 .east = some 268 := by decide +kernel
theorem advanceAt267_west : advance soko1_2.board 267 .west = some 266 := by decide +kernel
theorem advanceAt267_northEast : advance soko1_2.board 267 .northEast = some 242 := by decide +kernel
theorem advanceAt267_northWest : advance soko1_2.board 267 .northWest = some 240 := by decide +kernel
theorem advanceAt267_southEast : advance soko1_2.board 267 .southEast = some 294 := by decide +kernel
theorem advanceAt267_southWest : advance soko1_2.board 267 .southWest = some 292 := by decide +kernel
theorem floorAt268 : soko1_2.board.floor.contains 268 = false := by decide +kernel
theorem doorAt268 : soko1_2.board.doors.contains 268 = false := by decide +kernel
theorem trapAt268 : soko1_2.board.rollingTraps.contains 268 = false := by decide +kernel
theorem boxAt268 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 268 = false := rfl
theorem holeAt268 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 268 = false := rfl
theorem advanceAt268_north : advance soko1_2.board 268 .north = some 242 := by decide +kernel
theorem advanceAt268_south : advance soko1_2.board 268 .south = some 294 := by decide +kernel
theorem advanceAt268_east : advance soko1_2.board 268 .east = some 269 := by decide +kernel
theorem advanceAt268_west : advance soko1_2.board 268 .west = some 267 := by decide +kernel
theorem advanceAt268_northEast : advance soko1_2.board 268 .northEast = some 243 := by decide +kernel
theorem advanceAt268_northWest : advance soko1_2.board 268 .northWest = some 241 := by decide +kernel
theorem advanceAt268_southEast : advance soko1_2.board 268 .southEast = some 295 := by decide +kernel
theorem advanceAt268_southWest : advance soko1_2.board 268 .southWest = some 293 := by decide +kernel
theorem floorAt269 : soko1_2.board.floor.contains 269 = false := by decide +kernel
theorem doorAt269 : soko1_2.board.doors.contains 269 = false := by decide +kernel
theorem trapAt269 : soko1_2.board.rollingTraps.contains 269 = false := by decide +kernel
theorem boxAt269 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 269 = false := rfl
theorem holeAt269 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 269 = false := rfl
theorem advanceAt269_north : advance soko1_2.board 269 .north = some 243 := by decide +kernel
theorem advanceAt269_south : advance soko1_2.board 269 .south = some 295 := by decide +kernel
theorem advanceAt269_east : advance soko1_2.board 269 .east = some 270 := by decide +kernel
theorem advanceAt269_west : advance soko1_2.board 269 .west = some 268 := by decide +kernel
theorem advanceAt269_northEast : advance soko1_2.board 269 .northEast = some 244 := by decide +kernel
theorem advanceAt269_northWest : advance soko1_2.board 269 .northWest = some 242 := by decide +kernel
theorem advanceAt269_southEast : advance soko1_2.board 269 .southEast = some 296 := by decide +kernel
theorem advanceAt269_southWest : advance soko1_2.board 269 .southWest = some 294 := by decide +kernel
theorem floorAt270 : soko1_2.board.floor.contains 270 = true := by decide +kernel
theorem doorAt270 : soko1_2.board.doors.contains 270 = false := by decide +kernel
theorem trapAt270 : soko1_2.board.rollingTraps.contains 270 = false := by decide +kernel
theorem boxAt270 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 270 = p 270 := rfl
theorem holeAt270 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 270 = false := rfl
theorem advanceAt270_north : advance soko1_2.board 270 .north = some 244 := by decide +kernel
theorem advanceAt270_south : advance soko1_2.board 270 .south = some 296 := by decide +kernel
theorem advanceAt270_east : advance soko1_2.board 270 .east = some 271 := by decide +kernel
theorem advanceAt270_west : advance soko1_2.board 270 .west = some 269 := by decide +kernel
theorem advanceAt270_northEast : advance soko1_2.board 270 .northEast = some 245 := by decide +kernel
theorem advanceAt270_northWest : advance soko1_2.board 270 .northWest = some 243 := by decide +kernel
theorem advanceAt270_southEast : advance soko1_2.board 270 .southEast = some 297 := by decide +kernel
theorem advanceAt270_southWest : advance soko1_2.board 270 .southWest = some 295 := by decide +kernel
theorem floorAt271 : soko1_2.board.floor.contains 271 = true := by decide +kernel
theorem doorAt271 : soko1_2.board.doors.contains 271 = false := by decide +kernel
theorem trapAt271 : soko1_2.board.rollingTraps.contains 271 = false := by decide +kernel
theorem boxAt271 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 271 = p 271 := rfl
theorem holeAt271 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 271 = false := rfl
theorem advanceAt271_north : advance soko1_2.board 271 .north = some 245 := by decide +kernel
theorem advanceAt271_south : advance soko1_2.board 271 .south = some 297 := by decide +kernel
theorem advanceAt271_east : advance soko1_2.board 271 .east = some 272 := by decide +kernel
theorem advanceAt271_west : advance soko1_2.board 271 .west = some 270 := by decide +kernel
theorem advanceAt271_northEast : advance soko1_2.board 271 .northEast = some 246 := by decide +kernel
theorem advanceAt271_northWest : advance soko1_2.board 271 .northWest = some 244 := by decide +kernel
theorem advanceAt271_southEast : advance soko1_2.board 271 .southEast = some 298 := by decide +kernel
theorem advanceAt271_southWest : advance soko1_2.board 271 .southWest = some 296 := by decide +kernel
theorem floorAt272 : soko1_2.board.floor.contains 272 = true := by decide +kernel
theorem doorAt272 : soko1_2.board.doors.contains 272 = false := by decide +kernel
theorem trapAt272 : soko1_2.board.rollingTraps.contains 272 = false := by decide +kernel
theorem boxAt272 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 272 = p 272 := rfl
theorem holeAt272 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 272 = false := rfl
theorem advanceAt272_north : advance soko1_2.board 272 .north = some 246 := by decide +kernel
theorem advanceAt272_south : advance soko1_2.board 272 .south = some 298 := by decide +kernel
theorem advanceAt272_east : advance soko1_2.board 272 .east = some 273 := by decide +kernel
theorem advanceAt272_west : advance soko1_2.board 272 .west = some 271 := by decide +kernel
theorem advanceAt272_northEast : advance soko1_2.board 272 .northEast = some 247 := by decide +kernel
theorem advanceAt272_northWest : advance soko1_2.board 272 .northWest = some 245 := by decide +kernel
theorem advanceAt272_southEast : advance soko1_2.board 272 .southEast = some 299 := by decide +kernel
theorem advanceAt272_southWest : advance soko1_2.board 272 .southWest = some 297 := by decide +kernel
theorem floorAt273 : soko1_2.board.floor.contains 273 = false := by decide +kernel
theorem doorAt273 : soko1_2.board.doors.contains 273 = false := by decide +kernel
theorem trapAt273 : soko1_2.board.rollingTraps.contains 273 = false := by decide +kernel
theorem boxAt273 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 273 = false := rfl
theorem holeAt273 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 273 = false := rfl
theorem advanceAt273_north : advance soko1_2.board 273 .north = some 247 := by decide +kernel
theorem advanceAt273_south : advance soko1_2.board 273 .south = some 299 := by decide +kernel
theorem advanceAt273_east : advance soko1_2.board 273 .east = some 274 := by decide +kernel
theorem advanceAt273_west : advance soko1_2.board 273 .west = some 272 := by decide +kernel
theorem advanceAt273_northEast : advance soko1_2.board 273 .northEast = some 248 := by decide +kernel
theorem advanceAt273_northWest : advance soko1_2.board 273 .northWest = some 246 := by decide +kernel
theorem advanceAt273_southEast : advance soko1_2.board 273 .southEast = some 300 := by decide +kernel
theorem advanceAt273_southWest : advance soko1_2.board 273 .southWest = some 298 := by decide +kernel
theorem floorAt274 : soko1_2.board.floor.contains 274 = false := by decide +kernel
theorem doorAt274 : soko1_2.board.doors.contains 274 = false := by decide +kernel
theorem trapAt274 : soko1_2.board.rollingTraps.contains 274 = false := by decide +kernel
theorem boxAt274 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 274 = false := rfl
theorem holeAt274 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 274 = false := rfl
theorem advanceAt274_north : advance soko1_2.board 274 .north = some 248 := by decide +kernel
theorem advanceAt274_south : advance soko1_2.board 274 .south = some 300 := by decide +kernel
theorem advanceAt274_east : advance soko1_2.board 274 .east = some 275 := by decide +kernel
theorem advanceAt274_west : advance soko1_2.board 274 .west = some 273 := by decide +kernel
theorem advanceAt274_northEast : advance soko1_2.board 274 .northEast = some 249 := by decide +kernel
theorem advanceAt274_northWest : advance soko1_2.board 274 .northWest = some 247 := by decide +kernel
theorem advanceAt274_southEast : advance soko1_2.board 274 .southEast = some 301 := by decide +kernel
theorem advanceAt274_southWest : advance soko1_2.board 274 .southWest = some 299 := by decide +kernel
theorem floorAt275 : soko1_2.board.floor.contains 275 = false := by decide +kernel
theorem doorAt275 : soko1_2.board.doors.contains 275 = false := by decide +kernel
theorem trapAt275 : soko1_2.board.rollingTraps.contains 275 = false := by decide +kernel
theorem boxAt275 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 275 = false := rfl
theorem holeAt275 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 275 = false := rfl
theorem advanceAt275_north : advance soko1_2.board 275 .north = some 249 := by decide +kernel
theorem advanceAt275_south : advance soko1_2.board 275 .south = some 301 := by decide +kernel
theorem advanceAt275_east : advance soko1_2.board 275 .east = some 276 := by decide +kernel
theorem advanceAt275_west : advance soko1_2.board 275 .west = some 274 := by decide +kernel
theorem advanceAt275_northEast : advance soko1_2.board 275 .northEast = some 250 := by decide +kernel
theorem advanceAt275_northWest : advance soko1_2.board 275 .northWest = some 248 := by decide +kernel
theorem advanceAt275_southEast : advance soko1_2.board 275 .southEast = some 302 := by decide +kernel
theorem advanceAt275_southWest : advance soko1_2.board 275 .southWest = some 300 := by decide +kernel
theorem floorAt276 : soko1_2.board.floor.contains 276 = true := by decide +kernel
theorem doorAt276 : soko1_2.board.doors.contains 276 = false := by decide +kernel
theorem trapAt276 : soko1_2.board.rollingTraps.contains 276 = false := by decide +kernel
theorem boxAt276 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 276 = false := rfl
theorem holeAt276 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 276 = false := rfl
theorem advanceAt276_north : advance soko1_2.board 276 .north = some 250 := by decide +kernel
theorem advanceAt276_south : advance soko1_2.board 276 .south = some 302 := by decide +kernel
theorem advanceAt276_east : advance soko1_2.board 276 .east = some 277 := by decide +kernel
theorem advanceAt276_west : advance soko1_2.board 276 .west = some 275 := by decide +kernel
theorem advanceAt276_northEast : advance soko1_2.board 276 .northEast = some 251 := by decide +kernel
theorem advanceAt276_northWest : advance soko1_2.board 276 .northWest = some 249 := by decide +kernel
theorem advanceAt276_southEast : advance soko1_2.board 276 .southEast = some 303 := by decide +kernel
theorem advanceAt276_southWest : advance soko1_2.board 276 .southWest = some 301 := by decide +kernel
theorem floorAt277 : soko1_2.board.floor.contains 277 = false := by decide +kernel
theorem doorAt277 : soko1_2.board.doors.contains 277 = true := by decide +kernel
theorem trapAt277 : soko1_2.board.rollingTraps.contains 277 = false := by decide +kernel
theorem boxAt277 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 277 = false := rfl
theorem holeAt277 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 277 = false := rfl
theorem advanceAt277_north : advance soko1_2.board 277 .north = some 251 := by decide +kernel
theorem advanceAt277_south : advance soko1_2.board 277 .south = some 303 := by decide +kernel
theorem advanceAt277_east : advance soko1_2.board 277 .east = some 278 := by decide +kernel
theorem advanceAt277_west : advance soko1_2.board 277 .west = some 276 := by decide +kernel
theorem advanceAt277_northEast : advance soko1_2.board 277 .northEast = some 252 := by decide +kernel
theorem advanceAt277_northWest : advance soko1_2.board 277 .northWest = some 250 := by decide +kernel
theorem advanceAt277_southEast : advance soko1_2.board 277 .southEast = some 304 := by decide +kernel
theorem advanceAt277_southWest : advance soko1_2.board 277 .southWest = some 302 := by decide +kernel
theorem floorAt278 : soko1_2.board.floor.contains 278 = true := by decide +kernel
theorem doorAt278 : soko1_2.board.doors.contains 278 = false := by decide +kernel
theorem trapAt278 : soko1_2.board.rollingTraps.contains 278 = false := by decide +kernel
theorem boxAt278 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 278 = false := rfl
theorem holeAt278 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 278 = false := rfl
theorem advanceAt278_north : advance soko1_2.board 278 .north = some 252 := by decide +kernel
theorem advanceAt278_south : advance soko1_2.board 278 .south = some 304 := by decide +kernel
theorem advanceAt278_east : advance soko1_2.board 278 .east = some 279 := by decide +kernel
theorem advanceAt278_west : advance soko1_2.board 278 .west = some 277 := by decide +kernel
theorem advanceAt278_northEast : advance soko1_2.board 278 .northEast = some 253 := by decide +kernel
theorem advanceAt278_northWest : advance soko1_2.board 278 .northWest = some 251 := by decide +kernel
theorem advanceAt278_southEast : advance soko1_2.board 278 .southEast = some 305 := by decide +kernel
theorem advanceAt278_southWest : advance soko1_2.board 278 .southWest = some 303 := by decide +kernel
theorem floorAt279 : soko1_2.board.floor.contains 279 = true := by decide +kernel
theorem doorAt279 : soko1_2.board.doors.contains 279 = false := by decide +kernel
theorem trapAt279 : soko1_2.board.rollingTraps.contains 279 = false := by decide +kernel
theorem boxAt279 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 279 = false := rfl
theorem holeAt279 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 279 = false := rfl
theorem advanceAt279_north : advance soko1_2.board 279 .north = some 253 := by decide +kernel
theorem advanceAt279_south : advance soko1_2.board 279 .south = some 305 := by decide +kernel
theorem advanceAt279_east : advance soko1_2.board 279 .east = some 280 := by decide +kernel
theorem advanceAt279_west : advance soko1_2.board 279 .west = some 278 := by decide +kernel
theorem advanceAt279_northEast : advance soko1_2.board 279 .northEast = some 254 := by decide +kernel
theorem advanceAt279_northWest : advance soko1_2.board 279 .northWest = some 252 := by decide +kernel
theorem advanceAt279_southEast : advance soko1_2.board 279 .southEast = some 306 := by decide +kernel
theorem advanceAt279_southWest : advance soko1_2.board 279 .southWest = some 304 := by decide +kernel
end NetHack.Soko12Forward220.Unified.P04
