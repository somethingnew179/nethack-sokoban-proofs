import NetHack.Soko12Forward220.Unified.P04.OracleCells04
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P04
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem floorAt200 : soko1_2.board.floor.contains 200 = false := by decide +kernel
theorem doorAt200 : soko1_2.board.doors.contains 200 = false := by decide +kernel
theorem trapAt200 : soko1_2.board.rollingTraps.contains 200 = false := by decide +kernel
theorem boxAt200 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 200 = false := rfl
theorem holeAt200 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 200 = false := rfl
theorem advanceAt200_north : advance soko1_2.board 200 .north = some 174 := by decide +kernel
theorem advanceAt200_south : advance soko1_2.board 200 .south = some 226 := by decide +kernel
theorem advanceAt200_east : advance soko1_2.board 200 .east = some 201 := by decide +kernel
theorem advanceAt200_west : advance soko1_2.board 200 .west = some 199 := by decide +kernel
theorem advanceAt200_northEast : advance soko1_2.board 200 .northEast = some 175 := by decide +kernel
theorem advanceAt200_northWest : advance soko1_2.board 200 .northWest = some 173 := by decide +kernel
theorem advanceAt200_southEast : advance soko1_2.board 200 .southEast = some 227 := by decide +kernel
theorem advanceAt200_southWest : advance soko1_2.board 200 .southWest = some 225 := by decide +kernel
theorem floorAt201 : soko1_2.board.floor.contains 201 = false := by decide +kernel
theorem doorAt201 : soko1_2.board.doors.contains 201 = false := by decide +kernel
theorem trapAt201 : soko1_2.board.rollingTraps.contains 201 = false := by decide +kernel
theorem boxAt201 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 201 = false := rfl
theorem holeAt201 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 201 = false := rfl
theorem advanceAt201_north : advance soko1_2.board 201 .north = some 175 := by decide +kernel
theorem advanceAt201_south : advance soko1_2.board 201 .south = some 227 := by decide +kernel
theorem advanceAt201_east : advance soko1_2.board 201 .east = some 202 := by decide +kernel
theorem advanceAt201_west : advance soko1_2.board 201 .west = some 200 := by decide +kernel
theorem advanceAt201_northEast : advance soko1_2.board 201 .northEast = some 176 := by decide +kernel
theorem advanceAt201_northWest : advance soko1_2.board 201 .northWest = some 174 := by decide +kernel
theorem advanceAt201_southEast : advance soko1_2.board 201 .southEast = some 228 := by decide +kernel
theorem advanceAt201_southWest : advance soko1_2.board 201 .southWest = some 226 := by decide +kernel
theorem floorAt202 : soko1_2.board.floor.contains 202 = false := by decide +kernel
theorem doorAt202 : soko1_2.board.doors.contains 202 = false := by decide +kernel
theorem trapAt202 : soko1_2.board.rollingTraps.contains 202 = false := by decide +kernel
theorem boxAt202 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 202 = false := rfl
theorem holeAt202 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 202 = false := rfl
theorem advanceAt202_north : advance soko1_2.board 202 .north = some 176 := by decide +kernel
theorem advanceAt202_south : advance soko1_2.board 202 .south = some 228 := by decide +kernel
theorem advanceAt202_east : advance soko1_2.board 202 .east = some 203 := by decide +kernel
theorem advanceAt202_west : advance soko1_2.board 202 .west = some 201 := by decide +kernel
theorem advanceAt202_northEast : advance soko1_2.board 202 .northEast = some 177 := by decide +kernel
theorem advanceAt202_northWest : advance soko1_2.board 202 .northWest = some 175 := by decide +kernel
theorem advanceAt202_southEast : advance soko1_2.board 202 .southEast = some 229 := by decide +kernel
theorem advanceAt202_southWest : advance soko1_2.board 202 .southWest = some 227 := by decide +kernel
theorem floorAt203 : soko1_2.board.floor.contains 203 = false := by decide +kernel
theorem doorAt203 : soko1_2.board.doors.contains 203 = false := by decide +kernel
theorem trapAt203 : soko1_2.board.rollingTraps.contains 203 = false := by decide +kernel
theorem boxAt203 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 203 = false := rfl
theorem holeAt203 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 203 = false := rfl
theorem advanceAt203_north : advance soko1_2.board 203 .north = some 177 := by decide +kernel
theorem advanceAt203_south : advance soko1_2.board 203 .south = some 229 := by decide +kernel
theorem advanceAt203_east : advance soko1_2.board 203 .east = some 204 := by decide +kernel
theorem advanceAt203_west : advance soko1_2.board 203 .west = some 202 := by decide +kernel
theorem advanceAt203_northEast : advance soko1_2.board 203 .northEast = some 178 := by decide +kernel
theorem advanceAt203_northWest : advance soko1_2.board 203 .northWest = some 176 := by decide +kernel
theorem advanceAt203_southEast : advance soko1_2.board 203 .southEast = some 230 := by decide +kernel
theorem advanceAt203_southWest : advance soko1_2.board 203 .southWest = some 228 := by decide +kernel
theorem floorAt204 : soko1_2.board.floor.contains 204 = false := by decide +kernel
theorem doorAt204 : soko1_2.board.doors.contains 204 = false := by decide +kernel
theorem trapAt204 : soko1_2.board.rollingTraps.contains 204 = false := by decide +kernel
theorem boxAt204 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 204 = false := rfl
theorem holeAt204 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 204 = false := rfl
theorem advanceAt204_north : advance soko1_2.board 204 .north = some 178 := by decide +kernel
theorem advanceAt204_south : advance soko1_2.board 204 .south = some 230 := by decide +kernel
theorem advanceAt204_east : advance soko1_2.board 204 .east = some 205 := by decide +kernel
theorem advanceAt204_west : advance soko1_2.board 204 .west = some 203 := by decide +kernel
theorem advanceAt204_northEast : advance soko1_2.board 204 .northEast = some 179 := by decide +kernel
theorem advanceAt204_northWest : advance soko1_2.board 204 .northWest = some 177 := by decide +kernel
theorem advanceAt204_southEast : advance soko1_2.board 204 .southEast = some 231 := by decide +kernel
theorem advanceAt204_southWest : advance soko1_2.board 204 .southWest = some 229 := by decide +kernel
theorem floorAt205 : soko1_2.board.floor.contains 205 = false := by decide +kernel
theorem doorAt205 : soko1_2.board.doors.contains 205 = false := by decide +kernel
theorem trapAt205 : soko1_2.board.rollingTraps.contains 205 = false := by decide +kernel
theorem boxAt205 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 205 = false := rfl
theorem holeAt205 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 205 = false := rfl
theorem advanceAt205_north : advance soko1_2.board 205 .north = some 179 := by decide +kernel
theorem advanceAt205_south : advance soko1_2.board 205 .south = some 231 := by decide +kernel
theorem advanceAt205_east : advance soko1_2.board 205 .east = some 206 := by decide +kernel
theorem advanceAt205_west : advance soko1_2.board 205 .west = some 204 := by decide +kernel
theorem advanceAt205_northEast : advance soko1_2.board 205 .northEast = some 180 := by decide +kernel
theorem advanceAt205_northWest : advance soko1_2.board 205 .northWest = some 178 := by decide +kernel
theorem advanceAt205_southEast : advance soko1_2.board 205 .southEast = some 232 := by decide +kernel
theorem advanceAt205_southWest : advance soko1_2.board 205 .southWest = some 230 := by decide +kernel
theorem floorAt206 : soko1_2.board.floor.contains 206 = true := by decide +kernel
theorem doorAt206 : soko1_2.board.doors.contains 206 = false := by decide +kernel
theorem trapAt206 : soko1_2.board.rollingTraps.contains 206 = false := by decide +kernel
theorem boxAt206 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 206 = false := rfl
theorem holeAt206 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 206 = false := rfl
theorem advanceAt206_north : advance soko1_2.board 206 .north = some 180 := by decide +kernel
theorem advanceAt206_south : advance soko1_2.board 206 .south = some 232 := by decide +kernel
theorem advanceAt206_east : advance soko1_2.board 206 .east = some 207 := by decide +kernel
theorem advanceAt206_west : advance soko1_2.board 206 .west = some 205 := by decide +kernel
theorem advanceAt206_northEast : advance soko1_2.board 206 .northEast = some 181 := by decide +kernel
theorem advanceAt206_northWest : advance soko1_2.board 206 .northWest = some 179 := by decide +kernel
theorem advanceAt206_southEast : advance soko1_2.board 206 .southEast = some 233 := by decide +kernel
theorem advanceAt206_southWest : advance soko1_2.board 206 .southWest = some 231 := by decide +kernel
theorem floorAt207 : soko1_2.board.floor.contains 207 = false := by decide +kernel
theorem doorAt207 : soko1_2.board.doors.contains 207 = false := by decide +kernel
theorem trapAt207 : soko1_2.board.rollingTraps.contains 207 = false := by decide +kernel
theorem boxAt207 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 207 = false := rfl
theorem holeAt207 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 207 = false := rfl
theorem advanceAt207_north : advance soko1_2.board 207 .north = some 181 := by decide +kernel
theorem advanceAt207_south : advance soko1_2.board 207 .south = some 233 := by decide +kernel
theorem advanceAt207_east : advance soko1_2.board 207 .east = none := by decide +kernel
theorem advanceAt207_west : advance soko1_2.board 207 .west = some 206 := by decide +kernel
theorem advanceAt207_northEast : advance soko1_2.board 207 .northEast = none := by decide +kernel
theorem advanceAt207_northWest : advance soko1_2.board 207 .northWest = some 180 := by decide +kernel
theorem advanceAt207_southEast : advance soko1_2.board 207 .southEast = none := by decide +kernel
theorem advanceAt207_southWest : advance soko1_2.board 207 .southWest = some 232 := by decide +kernel
theorem floorAt208 : soko1_2.board.floor.contains 208 = false := by decide +kernel
theorem doorAt208 : soko1_2.board.doors.contains 208 = false := by decide +kernel
theorem trapAt208 : soko1_2.board.rollingTraps.contains 208 = false := by decide +kernel
theorem boxAt208 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 208 = false := rfl
theorem holeAt208 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 208 = false := rfl
theorem advanceAt208_north : advance soko1_2.board 208 .north = some 182 := by decide +kernel
theorem advanceAt208_south : advance soko1_2.board 208 .south = some 234 := by decide +kernel
theorem advanceAt208_east : advance soko1_2.board 208 .east = some 209 := by decide +kernel
theorem advanceAt208_west : advance soko1_2.board 208 .west = none := by decide +kernel
theorem advanceAt208_northEast : advance soko1_2.board 208 .northEast = some 183 := by decide +kernel
theorem advanceAt208_northWest : advance soko1_2.board 208 .northWest = none := by decide +kernel
theorem advanceAt208_southEast : advance soko1_2.board 208 .southEast = some 235 := by decide +kernel
theorem advanceAt208_southWest : advance soko1_2.board 208 .southWest = none := by decide +kernel
theorem floorAt209 : soko1_2.board.floor.contains 209 = false := by decide +kernel
theorem doorAt209 : soko1_2.board.doors.contains 209 = false := by decide +kernel
theorem trapAt209 : soko1_2.board.rollingTraps.contains 209 = false := by decide +kernel
theorem boxAt209 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 209 = false := rfl
theorem holeAt209 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 209 = false := rfl
theorem advanceAt209_north : advance soko1_2.board 209 .north = some 183 := by decide +kernel
theorem advanceAt209_south : advance soko1_2.board 209 .south = some 235 := by decide +kernel
theorem advanceAt209_east : advance soko1_2.board 209 .east = some 210 := by decide +kernel
theorem advanceAt209_west : advance soko1_2.board 209 .west = some 208 := by decide +kernel
theorem advanceAt209_northEast : advance soko1_2.board 209 .northEast = some 184 := by decide +kernel
theorem advanceAt209_northWest : advance soko1_2.board 209 .northWest = some 182 := by decide +kernel
theorem advanceAt209_southEast : advance soko1_2.board 209 .southEast = some 236 := by decide +kernel
theorem advanceAt209_southWest : advance soko1_2.board 209 .southWest = some 234 := by decide +kernel
theorem floorAt210 : soko1_2.board.floor.contains 210 = true := by decide +kernel
theorem doorAt210 : soko1_2.board.doors.contains 210 = false := by decide +kernel
theorem trapAt210 : soko1_2.board.rollingTraps.contains 210 = false := by decide +kernel
theorem boxAt210 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 210 = p 210 := rfl
theorem holeAt210 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 210 = false := rfl
theorem advanceAt210_north : advance soko1_2.board 210 .north = some 184 := by decide +kernel
theorem advanceAt210_south : advance soko1_2.board 210 .south = some 236 := by decide +kernel
theorem advanceAt210_east : advance soko1_2.board 210 .east = some 211 := by decide +kernel
theorem advanceAt210_west : advance soko1_2.board 210 .west = some 209 := by decide +kernel
theorem advanceAt210_northEast : advance soko1_2.board 210 .northEast = some 185 := by decide +kernel
theorem advanceAt210_northWest : advance soko1_2.board 210 .northWest = some 183 := by decide +kernel
theorem advanceAt210_southEast : advance soko1_2.board 210 .southEast = some 237 := by decide +kernel
theorem advanceAt210_southWest : advance soko1_2.board 210 .southWest = some 235 := by decide +kernel
theorem floorAt211 : soko1_2.board.floor.contains 211 = true := by decide +kernel
theorem doorAt211 : soko1_2.board.doors.contains 211 = false := by decide +kernel
theorem trapAt211 : soko1_2.board.rollingTraps.contains 211 = false := by decide +kernel
theorem boxAt211 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 211 = p 211 := rfl
theorem holeAt211 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 211 = false := rfl
theorem advanceAt211_north : advance soko1_2.board 211 .north = some 185 := by decide +kernel
theorem advanceAt211_south : advance soko1_2.board 211 .south = some 237 := by decide +kernel
theorem advanceAt211_east : advance soko1_2.board 211 .east = some 212 := by decide +kernel
theorem advanceAt211_west : advance soko1_2.board 211 .west = some 210 := by decide +kernel
theorem advanceAt211_northEast : advance soko1_2.board 211 .northEast = some 186 := by decide +kernel
theorem advanceAt211_northWest : advance soko1_2.board 211 .northWest = some 184 := by decide +kernel
theorem advanceAt211_southEast : advance soko1_2.board 211 .southEast = some 238 := by decide +kernel
theorem advanceAt211_southWest : advance soko1_2.board 211 .southWest = some 236 := by decide +kernel
theorem floorAt212 : soko1_2.board.floor.contains 212 = true := by decide +kernel
theorem doorAt212 : soko1_2.board.doors.contains 212 = false := by decide +kernel
theorem trapAt212 : soko1_2.board.rollingTraps.contains 212 = false := by decide +kernel
theorem boxAt212 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 212 = p 212 := rfl
theorem holeAt212 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 212 = false := rfl
theorem advanceAt212_north : advance soko1_2.board 212 .north = some 186 := by decide +kernel
theorem advanceAt212_south : advance soko1_2.board 212 .south = some 238 := by decide +kernel
theorem advanceAt212_east : advance soko1_2.board 212 .east = some 213 := by decide +kernel
theorem advanceAt212_west : advance soko1_2.board 212 .west = some 211 := by decide +kernel
theorem advanceAt212_northEast : advance soko1_2.board 212 .northEast = some 187 := by decide +kernel
theorem advanceAt212_northWest : advance soko1_2.board 212 .northWest = some 185 := by decide +kernel
theorem advanceAt212_southEast : advance soko1_2.board 212 .southEast = some 239 := by decide +kernel
theorem advanceAt212_southWest : advance soko1_2.board 212 .southWest = some 237 := by decide +kernel
theorem floorAt213 : soko1_2.board.floor.contains 213 = true := by decide +kernel
theorem doorAt213 : soko1_2.board.doors.contains 213 = false := by decide +kernel
theorem trapAt213 : soko1_2.board.rollingTraps.contains 213 = false := by decide +kernel
theorem boxAt213 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 213 = p 213 := rfl
theorem holeAt213 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 213 = false := rfl
theorem advanceAt213_north : advance soko1_2.board 213 .north = some 187 := by decide +kernel
theorem advanceAt213_south : advance soko1_2.board 213 .south = some 239 := by decide +kernel
theorem advanceAt213_east : advance soko1_2.board 213 .east = some 214 := by decide +kernel
theorem advanceAt213_west : advance soko1_2.board 213 .west = some 212 := by decide +kernel
theorem advanceAt213_northEast : advance soko1_2.board 213 .northEast = some 188 := by decide +kernel
theorem advanceAt213_northWest : advance soko1_2.board 213 .northWest = some 186 := by decide +kernel
theorem advanceAt213_southEast : advance soko1_2.board 213 .southEast = some 240 := by decide +kernel
theorem advanceAt213_southWest : advance soko1_2.board 213 .southWest = some 238 := by decide +kernel
theorem floorAt214 : soko1_2.board.floor.contains 214 = true := by decide +kernel
theorem doorAt214 : soko1_2.board.doors.contains 214 = false := by decide +kernel
theorem trapAt214 : soko1_2.board.rollingTraps.contains 214 = false := by decide +kernel
theorem boxAt214 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 214 = p 214 := rfl
theorem holeAt214 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 214 = false := rfl
theorem advanceAt214_north : advance soko1_2.board 214 .north = some 188 := by decide +kernel
theorem advanceAt214_south : advance soko1_2.board 214 .south = some 240 := by decide +kernel
theorem advanceAt214_east : advance soko1_2.board 214 .east = some 215 := by decide +kernel
theorem advanceAt214_west : advance soko1_2.board 214 .west = some 213 := by decide +kernel
theorem advanceAt214_northEast : advance soko1_2.board 214 .northEast = some 189 := by decide +kernel
theorem advanceAt214_northWest : advance soko1_2.board 214 .northWest = some 187 := by decide +kernel
theorem advanceAt214_southEast : advance soko1_2.board 214 .southEast = some 241 := by decide +kernel
theorem advanceAt214_southWest : advance soko1_2.board 214 .southWest = some 239 := by decide +kernel
theorem floorAt215 : soko1_2.board.floor.contains 215 = true := by decide +kernel
theorem doorAt215 : soko1_2.board.doors.contains 215 = false := by decide +kernel
theorem trapAt215 : soko1_2.board.rollingTraps.contains 215 = false := by decide +kernel
theorem boxAt215 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 215 = p 215 := rfl
theorem holeAt215 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 215 = false := rfl
theorem advanceAt215_north : advance soko1_2.board 215 .north = some 189 := by decide +kernel
theorem advanceAt215_south : advance soko1_2.board 215 .south = some 241 := by decide +kernel
theorem advanceAt215_east : advance soko1_2.board 215 .east = some 216 := by decide +kernel
theorem advanceAt215_west : advance soko1_2.board 215 .west = some 214 := by decide +kernel
theorem advanceAt215_northEast : advance soko1_2.board 215 .northEast = some 190 := by decide +kernel
theorem advanceAt215_northWest : advance soko1_2.board 215 .northWest = some 188 := by decide +kernel
theorem advanceAt215_southEast : advance soko1_2.board 215 .southEast = some 242 := by decide +kernel
theorem advanceAt215_southWest : advance soko1_2.board 215 .southWest = some 240 := by decide +kernel
theorem floorAt216 : soko1_2.board.floor.contains 216 = true := by decide +kernel
theorem doorAt216 : soko1_2.board.doors.contains 216 = false := by decide +kernel
theorem trapAt216 : soko1_2.board.rollingTraps.contains 216 = false := by decide +kernel
theorem boxAt216 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 216 = p 216 := rfl
theorem holeAt216 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 216 = false := rfl
theorem advanceAt216_north : advance soko1_2.board 216 .north = some 190 := by decide +kernel
theorem advanceAt216_south : advance soko1_2.board 216 .south = some 242 := by decide +kernel
theorem advanceAt216_east : advance soko1_2.board 216 .east = some 217 := by decide +kernel
theorem advanceAt216_west : advance soko1_2.board 216 .west = some 215 := by decide +kernel
theorem advanceAt216_northEast : advance soko1_2.board 216 .northEast = some 191 := by decide +kernel
theorem advanceAt216_northWest : advance soko1_2.board 216 .northWest = some 189 := by decide +kernel
theorem advanceAt216_southEast : advance soko1_2.board 216 .southEast = some 243 := by decide +kernel
theorem advanceAt216_southWest : advance soko1_2.board 216 .southWest = some 241 := by decide +kernel
theorem floorAt217 : soko1_2.board.floor.contains 217 = false := by decide +kernel
theorem doorAt217 : soko1_2.board.doors.contains 217 = false := by decide +kernel
theorem trapAt217 : soko1_2.board.rollingTraps.contains 217 = false := by decide +kernel
theorem boxAt217 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 217 = false := rfl
theorem holeAt217 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 217 = false := rfl
theorem advanceAt217_north : advance soko1_2.board 217 .north = some 191 := by decide +kernel
theorem advanceAt217_south : advance soko1_2.board 217 .south = some 243 := by decide +kernel
theorem advanceAt217_east : advance soko1_2.board 217 .east = some 218 := by decide +kernel
theorem advanceAt217_west : advance soko1_2.board 217 .west = some 216 := by decide +kernel
theorem advanceAt217_northEast : advance soko1_2.board 217 .northEast = some 192 := by decide +kernel
theorem advanceAt217_northWest : advance soko1_2.board 217 .northWest = some 190 := by decide +kernel
theorem advanceAt217_southEast : advance soko1_2.board 217 .southEast = some 244 := by decide +kernel
theorem advanceAt217_southWest : advance soko1_2.board 217 .southWest = some 242 := by decide +kernel
theorem floorAt218 : soko1_2.board.floor.contains 218 = true := by decide +kernel
theorem doorAt218 : soko1_2.board.doors.contains 218 = false := by decide +kernel
theorem trapAt218 : soko1_2.board.rollingTraps.contains 218 = false := by decide +kernel
theorem boxAt218 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 218 = p 218 := rfl
theorem holeAt218 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 218 = false := rfl
theorem advanceAt218_north : advance soko1_2.board 218 .north = some 192 := by decide +kernel
theorem advanceAt218_south : advance soko1_2.board 218 .south = some 244 := by decide +kernel
theorem advanceAt218_east : advance soko1_2.board 218 .east = some 219 := by decide +kernel
theorem advanceAt218_west : advance soko1_2.board 218 .west = some 217 := by decide +kernel
theorem advanceAt218_northEast : advance soko1_2.board 218 .northEast = some 193 := by decide +kernel
theorem advanceAt218_northWest : advance soko1_2.board 218 .northWest = some 191 := by decide +kernel
theorem advanceAt218_southEast : advance soko1_2.board 218 .southEast = some 245 := by decide +kernel
theorem advanceAt218_southWest : advance soko1_2.board 218 .southWest = some 243 := by decide +kernel
theorem floorAt219 : soko1_2.board.floor.contains 219 = true := by decide +kernel
theorem doorAt219 : soko1_2.board.doors.contains 219 = false := by decide +kernel
theorem trapAt219 : soko1_2.board.rollingTraps.contains 219 = false := by decide +kernel
theorem boxAt219 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 219 = p 219 := rfl
theorem holeAt219 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 219 = false := rfl
theorem advanceAt219_north : advance soko1_2.board 219 .north = some 193 := by decide +kernel
theorem advanceAt219_south : advance soko1_2.board 219 .south = some 245 := by decide +kernel
theorem advanceAt219_east : advance soko1_2.board 219 .east = some 220 := by decide +kernel
theorem advanceAt219_west : advance soko1_2.board 219 .west = some 218 := by decide +kernel
theorem advanceAt219_northEast : advance soko1_2.board 219 .northEast = some 194 := by decide +kernel
theorem advanceAt219_northWest : advance soko1_2.board 219 .northWest = some 192 := by decide +kernel
theorem advanceAt219_southEast : advance soko1_2.board 219 .southEast = some 246 := by decide +kernel
theorem advanceAt219_southWest : advance soko1_2.board 219 .southWest = some 244 := by decide +kernel
theorem floorAt220 : soko1_2.board.floor.contains 220 = true := by decide +kernel
theorem doorAt220 : soko1_2.board.doors.contains 220 = false := by decide +kernel
theorem trapAt220 : soko1_2.board.rollingTraps.contains 220 = false := by decide +kernel
theorem boxAt220 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 220 = p 220 := rfl
theorem holeAt220 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 220 = false := rfl
theorem advanceAt220_north : advance soko1_2.board 220 .north = some 194 := by decide +kernel
theorem advanceAt220_south : advance soko1_2.board 220 .south = some 246 := by decide +kernel
theorem advanceAt220_east : advance soko1_2.board 220 .east = some 221 := by decide +kernel
theorem advanceAt220_west : advance soko1_2.board 220 .west = some 219 := by decide +kernel
theorem advanceAt220_northEast : advance soko1_2.board 220 .northEast = some 195 := by decide +kernel
theorem advanceAt220_northWest : advance soko1_2.board 220 .northWest = some 193 := by decide +kernel
theorem advanceAt220_southEast : advance soko1_2.board 220 .southEast = some 247 := by decide +kernel
theorem advanceAt220_southWest : advance soko1_2.board 220 .southWest = some 245 := by decide +kernel
theorem floorAt221 : soko1_2.board.floor.contains 221 = false := by decide +kernel
theorem doorAt221 : soko1_2.board.doors.contains 221 = false := by decide +kernel
theorem trapAt221 : soko1_2.board.rollingTraps.contains 221 = false := by decide +kernel
theorem boxAt221 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 221 = false := rfl
theorem holeAt221 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 221 = false := rfl
theorem advanceAt221_north : advance soko1_2.board 221 .north = some 195 := by decide +kernel
theorem advanceAt221_south : advance soko1_2.board 221 .south = some 247 := by decide +kernel
theorem advanceAt221_east : advance soko1_2.board 221 .east = some 222 := by decide +kernel
theorem advanceAt221_west : advance soko1_2.board 221 .west = some 220 := by decide +kernel
theorem advanceAt221_northEast : advance soko1_2.board 221 .northEast = some 196 := by decide +kernel
theorem advanceAt221_northWest : advance soko1_2.board 221 .northWest = some 194 := by decide +kernel
theorem advanceAt221_southEast : advance soko1_2.board 221 .southEast = some 248 := by decide +kernel
theorem advanceAt221_southWest : advance soko1_2.board 221 .southWest = some 246 := by decide +kernel
theorem floorAt222 : soko1_2.board.floor.contains 222 = false := by decide +kernel
theorem doorAt222 : soko1_2.board.doors.contains 222 = false := by decide +kernel
theorem trapAt222 : soko1_2.board.rollingTraps.contains 222 = false := by decide +kernel
theorem boxAt222 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 222 = false := rfl
theorem holeAt222 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 222 = false := rfl
theorem advanceAt222_north : advance soko1_2.board 222 .north = some 196 := by decide +kernel
theorem advanceAt222_south : advance soko1_2.board 222 .south = some 248 := by decide +kernel
theorem advanceAt222_east : advance soko1_2.board 222 .east = some 223 := by decide +kernel
theorem advanceAt222_west : advance soko1_2.board 222 .west = some 221 := by decide +kernel
theorem advanceAt222_northEast : advance soko1_2.board 222 .northEast = some 197 := by decide +kernel
theorem advanceAt222_northWest : advance soko1_2.board 222 .northWest = some 195 := by decide +kernel
theorem advanceAt222_southEast : advance soko1_2.board 222 .southEast = some 249 := by decide +kernel
theorem advanceAt222_southWest : advance soko1_2.board 222 .southWest = some 247 := by decide +kernel
theorem floorAt223 : soko1_2.board.floor.contains 223 = false := by decide +kernel
theorem doorAt223 : soko1_2.board.doors.contains 223 = false := by decide +kernel
theorem trapAt223 : soko1_2.board.rollingTraps.contains 223 = false := by decide +kernel
theorem boxAt223 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 223 = false := rfl
theorem holeAt223 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 223 = false := rfl
theorem advanceAt223_north : advance soko1_2.board 223 .north = some 197 := by decide +kernel
theorem advanceAt223_south : advance soko1_2.board 223 .south = some 249 := by decide +kernel
theorem advanceAt223_east : advance soko1_2.board 223 .east = some 224 := by decide +kernel
theorem advanceAt223_west : advance soko1_2.board 223 .west = some 222 := by decide +kernel
theorem advanceAt223_northEast : advance soko1_2.board 223 .northEast = some 198 := by decide +kernel
theorem advanceAt223_northWest : advance soko1_2.board 223 .northWest = some 196 := by decide +kernel
theorem advanceAt223_southEast : advance soko1_2.board 223 .southEast = some 250 := by decide +kernel
theorem advanceAt223_southWest : advance soko1_2.board 223 .southWest = some 248 := by decide +kernel
theorem floorAt224 : soko1_2.board.floor.contains 224 = false := by decide +kernel
theorem doorAt224 : soko1_2.board.doors.contains 224 = false := by decide +kernel
theorem trapAt224 : soko1_2.board.rollingTraps.contains 224 = false := by decide +kernel
theorem boxAt224 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 224 = false := rfl
theorem holeAt224 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 224 = false := rfl
theorem advanceAt224_north : advance soko1_2.board 224 .north = some 198 := by decide +kernel
theorem advanceAt224_south : advance soko1_2.board 224 .south = some 250 := by decide +kernel
theorem advanceAt224_east : advance soko1_2.board 224 .east = some 225 := by decide +kernel
theorem advanceAt224_west : advance soko1_2.board 224 .west = some 223 := by decide +kernel
theorem advanceAt224_northEast : advance soko1_2.board 224 .northEast = some 199 := by decide +kernel
theorem advanceAt224_northWest : advance soko1_2.board 224 .northWest = some 197 := by decide +kernel
theorem advanceAt224_southEast : advance soko1_2.board 224 .southEast = some 251 := by decide +kernel
theorem advanceAt224_southWest : advance soko1_2.board 224 .southWest = some 249 := by decide +kernel
theorem floorAt225 : soko1_2.board.floor.contains 225 = false := by decide +kernel
theorem doorAt225 : soko1_2.board.doors.contains 225 = false := by decide +kernel
theorem trapAt225 : soko1_2.board.rollingTraps.contains 225 = false := by decide +kernel
theorem boxAt225 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 225 = false := rfl
theorem holeAt225 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 225 = false := rfl
theorem advanceAt225_north : advance soko1_2.board 225 .north = some 199 := by decide +kernel
theorem advanceAt225_south : advance soko1_2.board 225 .south = some 251 := by decide +kernel
theorem advanceAt225_east : advance soko1_2.board 225 .east = some 226 := by decide +kernel
theorem advanceAt225_west : advance soko1_2.board 225 .west = some 224 := by decide +kernel
theorem advanceAt225_northEast : advance soko1_2.board 225 .northEast = some 200 := by decide +kernel
theorem advanceAt225_northWest : advance soko1_2.board 225 .northWest = some 198 := by decide +kernel
theorem advanceAt225_southEast : advance soko1_2.board 225 .southEast = some 252 := by decide +kernel
theorem advanceAt225_southWest : advance soko1_2.board 225 .southWest = some 250 := by decide +kernel
theorem floorAt226 : soko1_2.board.floor.contains 226 = false := by decide +kernel
theorem doorAt226 : soko1_2.board.doors.contains 226 = false := by decide +kernel
theorem trapAt226 : soko1_2.board.rollingTraps.contains 226 = false := by decide +kernel
theorem boxAt226 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 226 = false := rfl
theorem holeAt226 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 226 = false := rfl
theorem advanceAt226_north : advance soko1_2.board 226 .north = some 200 := by decide +kernel
theorem advanceAt226_south : advance soko1_2.board 226 .south = some 252 := by decide +kernel
theorem advanceAt226_east : advance soko1_2.board 226 .east = some 227 := by decide +kernel
theorem advanceAt226_west : advance soko1_2.board 226 .west = some 225 := by decide +kernel
theorem advanceAt226_northEast : advance soko1_2.board 226 .northEast = some 201 := by decide +kernel
theorem advanceAt226_northWest : advance soko1_2.board 226 .northWest = some 199 := by decide +kernel
theorem advanceAt226_southEast : advance soko1_2.board 226 .southEast = some 253 := by decide +kernel
theorem advanceAt226_southWest : advance soko1_2.board 226 .southWest = some 251 := by decide +kernel
theorem floorAt227 : soko1_2.board.floor.contains 227 = false := by decide +kernel
theorem doorAt227 : soko1_2.board.doors.contains 227 = false := by decide +kernel
theorem trapAt227 : soko1_2.board.rollingTraps.contains 227 = false := by decide +kernel
theorem boxAt227 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 227 = false := rfl
theorem holeAt227 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 227 = false := rfl
theorem advanceAt227_north : advance soko1_2.board 227 .north = some 201 := by decide +kernel
theorem advanceAt227_south : advance soko1_2.board 227 .south = some 253 := by decide +kernel
theorem advanceAt227_east : advance soko1_2.board 227 .east = some 228 := by decide +kernel
theorem advanceAt227_west : advance soko1_2.board 227 .west = some 226 := by decide +kernel
theorem advanceAt227_northEast : advance soko1_2.board 227 .northEast = some 202 := by decide +kernel
theorem advanceAt227_northWest : advance soko1_2.board 227 .northWest = some 200 := by decide +kernel
theorem advanceAt227_southEast : advance soko1_2.board 227 .southEast = some 254 := by decide +kernel
theorem advanceAt227_southWest : advance soko1_2.board 227 .southWest = some 252 := by decide +kernel
theorem floorAt228 : soko1_2.board.floor.contains 228 = false := by decide +kernel
theorem doorAt228 : soko1_2.board.doors.contains 228 = false := by decide +kernel
theorem trapAt228 : soko1_2.board.rollingTraps.contains 228 = false := by decide +kernel
theorem boxAt228 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 228 = false := rfl
theorem holeAt228 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 228 = false := rfl
theorem advanceAt228_north : advance soko1_2.board 228 .north = some 202 := by decide +kernel
theorem advanceAt228_south : advance soko1_2.board 228 .south = some 254 := by decide +kernel
theorem advanceAt228_east : advance soko1_2.board 228 .east = some 229 := by decide +kernel
theorem advanceAt228_west : advance soko1_2.board 228 .west = some 227 := by decide +kernel
theorem advanceAt228_northEast : advance soko1_2.board 228 .northEast = some 203 := by decide +kernel
theorem advanceAt228_northWest : advance soko1_2.board 228 .northWest = some 201 := by decide +kernel
theorem advanceAt228_southEast : advance soko1_2.board 228 .southEast = some 255 := by decide +kernel
theorem advanceAt228_southWest : advance soko1_2.board 228 .southWest = some 253 := by decide +kernel
theorem floorAt229 : soko1_2.board.floor.contains 229 = false := by decide +kernel
theorem doorAt229 : soko1_2.board.doors.contains 229 = false := by decide +kernel
theorem trapAt229 : soko1_2.board.rollingTraps.contains 229 = false := by decide +kernel
theorem boxAt229 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 229 = false := rfl
theorem holeAt229 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 229 = false := rfl
theorem advanceAt229_north : advance soko1_2.board 229 .north = some 203 := by decide +kernel
theorem advanceAt229_south : advance soko1_2.board 229 .south = some 255 := by decide +kernel
theorem advanceAt229_east : advance soko1_2.board 229 .east = some 230 := by decide +kernel
theorem advanceAt229_west : advance soko1_2.board 229 .west = some 228 := by decide +kernel
theorem advanceAt229_northEast : advance soko1_2.board 229 .northEast = some 204 := by decide +kernel
theorem advanceAt229_northWest : advance soko1_2.board 229 .northWest = some 202 := by decide +kernel
theorem advanceAt229_southEast : advance soko1_2.board 229 .southEast = some 256 := by decide +kernel
theorem advanceAt229_southWest : advance soko1_2.board 229 .southWest = some 254 := by decide +kernel
theorem floorAt230 : soko1_2.board.floor.contains 230 = false := by decide +kernel
theorem doorAt230 : soko1_2.board.doors.contains 230 = false := by decide +kernel
theorem trapAt230 : soko1_2.board.rollingTraps.contains 230 = false := by decide +kernel
theorem boxAt230 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 230 = false := rfl
theorem holeAt230 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 230 = false := rfl
theorem advanceAt230_north : advance soko1_2.board 230 .north = some 204 := by decide +kernel
theorem advanceAt230_south : advance soko1_2.board 230 .south = some 256 := by decide +kernel
theorem advanceAt230_east : advance soko1_2.board 230 .east = some 231 := by decide +kernel
theorem advanceAt230_west : advance soko1_2.board 230 .west = some 229 := by decide +kernel
theorem advanceAt230_northEast : advance soko1_2.board 230 .northEast = some 205 := by decide +kernel
theorem advanceAt230_northWest : advance soko1_2.board 230 .northWest = some 203 := by decide +kernel
theorem advanceAt230_southEast : advance soko1_2.board 230 .southEast = some 257 := by decide +kernel
theorem advanceAt230_southWest : advance soko1_2.board 230 .southWest = some 255 := by decide +kernel
theorem floorAt231 : soko1_2.board.floor.contains 231 = false := by decide +kernel
theorem doorAt231 : soko1_2.board.doors.contains 231 = false := by decide +kernel
theorem trapAt231 : soko1_2.board.rollingTraps.contains 231 = false := by decide +kernel
theorem boxAt231 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 231 = false := rfl
theorem holeAt231 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 231 = false := rfl
theorem advanceAt231_north : advance soko1_2.board 231 .north = some 205 := by decide +kernel
theorem advanceAt231_south : advance soko1_2.board 231 .south = some 257 := by decide +kernel
theorem advanceAt231_east : advance soko1_2.board 231 .east = some 232 := by decide +kernel
theorem advanceAt231_west : advance soko1_2.board 231 .west = some 230 := by decide +kernel
theorem advanceAt231_northEast : advance soko1_2.board 231 .northEast = some 206 := by decide +kernel
theorem advanceAt231_northWest : advance soko1_2.board 231 .northWest = some 204 := by decide +kernel
theorem advanceAt231_southEast : advance soko1_2.board 231 .southEast = some 258 := by decide +kernel
theorem advanceAt231_southWest : advance soko1_2.board 231 .southWest = some 256 := by decide +kernel
theorem floorAt232 : soko1_2.board.floor.contains 232 = true := by decide +kernel
theorem doorAt232 : soko1_2.board.doors.contains 232 = false := by decide +kernel
theorem trapAt232 : soko1_2.board.rollingTraps.contains 232 = false := by decide +kernel
theorem boxAt232 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 232 = false := rfl
theorem holeAt232 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 232 = false := rfl
theorem advanceAt232_north : advance soko1_2.board 232 .north = some 206 := by decide +kernel
theorem advanceAt232_south : advance soko1_2.board 232 .south = some 258 := by decide +kernel
theorem advanceAt232_east : advance soko1_2.board 232 .east = some 233 := by decide +kernel
theorem advanceAt232_west : advance soko1_2.board 232 .west = some 231 := by decide +kernel
theorem advanceAt232_northEast : advance soko1_2.board 232 .northEast = some 207 := by decide +kernel
theorem advanceAt232_northWest : advance soko1_2.board 232 .northWest = some 205 := by decide +kernel
theorem advanceAt232_southEast : advance soko1_2.board 232 .southEast = some 259 := by decide +kernel
theorem advanceAt232_southWest : advance soko1_2.board 232 .southWest = some 257 := by decide +kernel
theorem floorAt233 : soko1_2.board.floor.contains 233 = false := by decide +kernel
theorem doorAt233 : soko1_2.board.doors.contains 233 = false := by decide +kernel
theorem trapAt233 : soko1_2.board.rollingTraps.contains 233 = false := by decide +kernel
theorem boxAt233 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 233 = false := rfl
theorem holeAt233 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 233 = false := rfl
theorem advanceAt233_north : advance soko1_2.board 233 .north = some 207 := by decide +kernel
theorem advanceAt233_south : advance soko1_2.board 233 .south = some 259 := by decide +kernel
theorem advanceAt233_east : advance soko1_2.board 233 .east = none := by decide +kernel
theorem advanceAt233_west : advance soko1_2.board 233 .west = some 232 := by decide +kernel
theorem advanceAt233_northEast : advance soko1_2.board 233 .northEast = none := by decide +kernel
theorem advanceAt233_northWest : advance soko1_2.board 233 .northWest = some 206 := by decide +kernel
theorem advanceAt233_southEast : advance soko1_2.board 233 .southEast = none := by decide +kernel
theorem advanceAt233_southWest : advance soko1_2.board 233 .southWest = some 258 := by decide +kernel
theorem floorAt234 : soko1_2.board.floor.contains 234 = false := by decide +kernel
theorem doorAt234 : soko1_2.board.doors.contains 234 = false := by decide +kernel
theorem trapAt234 : soko1_2.board.rollingTraps.contains 234 = false := by decide +kernel
theorem boxAt234 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 234 = false := rfl
theorem holeAt234 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 234 = false := rfl
theorem advanceAt234_north : advance soko1_2.board 234 .north = some 208 := by decide +kernel
theorem advanceAt234_south : advance soko1_2.board 234 .south = some 260 := by decide +kernel
theorem advanceAt234_east : advance soko1_2.board 234 .east = some 235 := by decide +kernel
theorem advanceAt234_west : advance soko1_2.board 234 .west = none := by decide +kernel
theorem advanceAt234_northEast : advance soko1_2.board 234 .northEast = some 209 := by decide +kernel
theorem advanceAt234_northWest : advance soko1_2.board 234 .northWest = none := by decide +kernel
theorem advanceAt234_southEast : advance soko1_2.board 234 .southEast = some 261 := by decide +kernel
theorem advanceAt234_southWest : advance soko1_2.board 234 .southWest = none := by decide +kernel
theorem floorAt235 : soko1_2.board.floor.contains 235 = false := by decide +kernel
theorem doorAt235 : soko1_2.board.doors.contains 235 = false := by decide +kernel
theorem trapAt235 : soko1_2.board.rollingTraps.contains 235 = false := by decide +kernel
theorem boxAt235 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 235 = false := rfl
theorem holeAt235 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 235 = false := rfl
theorem advanceAt235_north : advance soko1_2.board 235 .north = some 209 := by decide +kernel
theorem advanceAt235_south : advance soko1_2.board 235 .south = some 261 := by decide +kernel
theorem advanceAt235_east : advance soko1_2.board 235 .east = some 236 := by decide +kernel
theorem advanceAt235_west : advance soko1_2.board 235 .west = some 234 := by decide +kernel
theorem advanceAt235_northEast : advance soko1_2.board 235 .northEast = some 210 := by decide +kernel
theorem advanceAt235_northWest : advance soko1_2.board 235 .northWest = some 208 := by decide +kernel
theorem advanceAt235_southEast : advance soko1_2.board 235 .southEast = some 262 := by decide +kernel
theorem advanceAt235_southWest : advance soko1_2.board 235 .southWest = some 260 := by decide +kernel
theorem floorAt236 : soko1_2.board.floor.contains 236 = true := by decide +kernel
theorem doorAt236 : soko1_2.board.doors.contains 236 = false := by decide +kernel
theorem trapAt236 : soko1_2.board.rollingTraps.contains 236 = false := by decide +kernel
theorem boxAt236 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 236 = p 236 := rfl
theorem holeAt236 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 236 = false := rfl
theorem advanceAt236_north : advance soko1_2.board 236 .north = some 210 := by decide +kernel
theorem advanceAt236_south : advance soko1_2.board 236 .south = some 262 := by decide +kernel
theorem advanceAt236_east : advance soko1_2.board 236 .east = some 237 := by decide +kernel
theorem advanceAt236_west : advance soko1_2.board 236 .west = some 235 := by decide +kernel
theorem advanceAt236_northEast : advance soko1_2.board 236 .northEast = some 211 := by decide +kernel
theorem advanceAt236_northWest : advance soko1_2.board 236 .northWest = some 209 := by decide +kernel
theorem advanceAt236_southEast : advance soko1_2.board 236 .southEast = some 263 := by decide +kernel
theorem advanceAt236_southWest : advance soko1_2.board 236 .southWest = some 261 := by decide +kernel
theorem floorAt237 : soko1_2.board.floor.contains 237 = true := by decide +kernel
theorem doorAt237 : soko1_2.board.doors.contains 237 = false := by decide +kernel
theorem trapAt237 : soko1_2.board.rollingTraps.contains 237 = false := by decide +kernel
theorem boxAt237 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 237 = p 237 := rfl
theorem holeAt237 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 237 = false := rfl
theorem advanceAt237_north : advance soko1_2.board 237 .north = some 211 := by decide +kernel
theorem advanceAt237_south : advance soko1_2.board 237 .south = some 263 := by decide +kernel
theorem advanceAt237_east : advance soko1_2.board 237 .east = some 238 := by decide +kernel
theorem advanceAt237_west : advance soko1_2.board 237 .west = some 236 := by decide +kernel
theorem advanceAt237_northEast : advance soko1_2.board 237 .northEast = some 212 := by decide +kernel
theorem advanceAt237_northWest : advance soko1_2.board 237 .northWest = some 210 := by decide +kernel
theorem advanceAt237_southEast : advance soko1_2.board 237 .southEast = some 264 := by decide +kernel
theorem advanceAt237_southWest : advance soko1_2.board 237 .southWest = some 262 := by decide +kernel
theorem floorAt238 : soko1_2.board.floor.contains 238 = true := by decide +kernel
theorem doorAt238 : soko1_2.board.doors.contains 238 = false := by decide +kernel
theorem trapAt238 : soko1_2.board.rollingTraps.contains 238 = false := by decide +kernel
theorem boxAt238 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 238 = p 238 := rfl
theorem holeAt238 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 238 = false := rfl
theorem advanceAt238_north : advance soko1_2.board 238 .north = some 212 := by decide +kernel
theorem advanceAt238_south : advance soko1_2.board 238 .south = some 264 := by decide +kernel
theorem advanceAt238_east : advance soko1_2.board 238 .east = some 239 := by decide +kernel
theorem advanceAt238_west : advance soko1_2.board 238 .west = some 237 := by decide +kernel
theorem advanceAt238_northEast : advance soko1_2.board 238 .northEast = some 213 := by decide +kernel
theorem advanceAt238_northWest : advance soko1_2.board 238 .northWest = some 211 := by decide +kernel
theorem advanceAt238_southEast : advance soko1_2.board 238 .southEast = some 265 := by decide +kernel
theorem advanceAt238_southWest : advance soko1_2.board 238 .southWest = some 263 := by decide +kernel
theorem floorAt239 : soko1_2.board.floor.contains 239 = true := by decide +kernel
theorem doorAt239 : soko1_2.board.doors.contains 239 = false := by decide +kernel
theorem trapAt239 : soko1_2.board.rollingTraps.contains 239 = false := by decide +kernel
theorem boxAt239 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p 239 = p 239 := rfl
theorem holeAt239 (p : Pattern) : project (soko1_2.initial.holes.drop 4) 239 = false := rfl
theorem advanceAt239_north : advance soko1_2.board 239 .north = some 213 := by decide +kernel
theorem advanceAt239_south : advance soko1_2.board 239 .south = some 265 := by decide +kernel
theorem advanceAt239_east : advance soko1_2.board 239 .east = some 240 := by decide +kernel
theorem advanceAt239_west : advance soko1_2.board 239 .west = some 238 := by decide +kernel
theorem advanceAt239_northEast : advance soko1_2.board 239 .northEast = some 214 := by decide +kernel
theorem advanceAt239_northWest : advance soko1_2.board 239 .northWest = some 212 := by decide +kernel
theorem advanceAt239_southEast : advance soko1_2.board 239 .southEast = some 266 := by decide +kernel
theorem advanceAt239_southWest : advance soko1_2.board 239 .southWest = some 264 := by decide +kernel
end NetHack.Soko12Forward220.Unified.P04
