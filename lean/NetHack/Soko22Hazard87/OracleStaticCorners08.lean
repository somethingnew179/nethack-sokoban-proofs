import NetHack.Soko22Hazard87.OracleStaticCorners07
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem cornerAt193_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 193 .north = false := rfl
theorem cornerAt193_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 193 .south = false := rfl
theorem cornerAt193_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 193 .east = false := rfl
theorem cornerAt193_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 193 .west = false := rfl
theorem cornerAt193_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 193 .northEast = (false && false) := rfl
theorem cornerAt193_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 193 .northWest = (false && false) := rfl
theorem cornerAt193_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 193 .southEast = (false && false) := rfl
theorem cornerAt193_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 193 .southWest = (false && false) := rfl
theorem cornerAt194_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 194 .north = false := rfl
theorem cornerAt194_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 194 .south = false := rfl
theorem cornerAt194_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 194 .east = false := rfl
theorem cornerAt194_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 194 .west = false := rfl
theorem cornerAt194_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 194 .northEast = (false && true) := rfl
theorem cornerAt194_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 194 .northWest = (false && false) := rfl
theorem cornerAt194_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 194 .southEast = (false && true) := rfl
theorem cornerAt194_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 194 .southWest = (false && false) := rfl
theorem cornerAt199_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 199 .north = false := rfl
theorem cornerAt199_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 199 .south = false := rfl
theorem cornerAt199_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 199 .east = false := rfl
theorem cornerAt199_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 199 .west = false := rfl
theorem cornerAt199_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 199 .northEast = (p 177 && p 200) := rfl
theorem cornerAt199_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 199 .northWest = (p 177 && true) := rfl
theorem cornerAt199_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 199 .southEast = (true && p 200) := rfl
theorem cornerAt199_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 199 .southWest = (true && true) := rfl
theorem cornerAt200_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 200 .north = false := rfl
theorem cornerAt200_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 200 .south = false := rfl
theorem cornerAt200_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 200 .east = false := rfl
theorem cornerAt200_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 200 .west = false := rfl
theorem cornerAt200_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 200 .northEast = (true && p 201) := rfl
theorem cornerAt200_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 200 .northWest = (true && p 199) := rfl
theorem cornerAt200_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 200 .southEast = (true && p 201) := rfl
theorem cornerAt200_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 200 .southWest = (true && p 199) := rfl
theorem cornerAt201_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 201 .north = false := rfl
theorem cornerAt201_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 201 .south = false := rfl
theorem cornerAt201_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 201 .east = false := rfl
theorem cornerAt201_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 201 .west = false := rfl
theorem cornerAt201_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 201 .northEast = (true && p 202) := rfl
theorem cornerAt201_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 201 .northWest = (true && p 200) := rfl
theorem cornerAt201_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 201 .southEast = (p 223 && p 202) := rfl
theorem cornerAt201_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 201 .southWest = (p 223 && p 200) := rfl
theorem cornerAt202_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 202 .north = false := rfl
theorem cornerAt202_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 202 .south = false := rfl
theorem cornerAt202_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 202 .east = false := rfl
theorem cornerAt202_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 202 .west = false := rfl
theorem cornerAt202_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 202 .northEast = (p 180 && true) := rfl
theorem cornerAt202_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 202 .northWest = (p 180 && p 201) := rfl
theorem cornerAt202_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 202 .southEast = (p 224 && true) := rfl
theorem cornerAt202_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 202 .southWest = (p 224 && p 201) := rfl
theorem cornerAt204_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 204 .north = false := rfl
theorem cornerAt204_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 204 .south = false := rfl
theorem cornerAt204_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 204 .east = false := rfl
theorem cornerAt204_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 204 .west = false := rfl
theorem cornerAt204_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 204 .northEast = (p 182 && true) := rfl
theorem cornerAt204_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 204 .northWest = (p 182 && true) := rfl
theorem cornerAt204_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 204 .southEast = (p 226 && true) := rfl
theorem cornerAt204_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 204 .southWest = (p 226 && true) := rfl
theorem cornerAt210_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 210 .north = false := rfl
theorem cornerAt210_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 210 .south = false := rfl
theorem cornerAt210_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 210 .east = false := rfl
theorem cornerAt210_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 210 .west = false := rfl
theorem cornerAt210_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 210 .northEast = (false && false) := rfl
theorem cornerAt210_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 210 .northWest = (false && true) := rfl
theorem cornerAt210_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 210 .southEast = (true && false) := rfl
theorem cornerAt210_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 210 .southWest = (true && true) := rfl
theorem cornerAt211_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 211 .north = false := rfl
theorem cornerAt211_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 211 .south = false := rfl
theorem cornerAt211_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 211 .east = false := rfl
theorem cornerAt211_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 211 .west = false := rfl
theorem cornerAt211_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 211 .northEast = (false && false) := rfl
theorem cornerAt211_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 211 .northWest = (false && false) := rfl
theorem cornerAt211_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 211 .southEast = (true && false) := rfl
theorem cornerAt211_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 211 .southWest = (true && false) := rfl
theorem cornerAt212_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 212 .north = false := rfl
theorem cornerAt212_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 212 .south = false := rfl
theorem cornerAt212_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 212 .east = false := rfl
theorem cornerAt212_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 212 .west = false := rfl
theorem cornerAt212_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 212 .northEast = (false && false) := rfl
theorem cornerAt212_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 212 .northWest = (false && false) := rfl
theorem cornerAt212_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 212 .southEast = (true && false) := rfl
theorem cornerAt212_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 212 .southWest = (true && false) := rfl
theorem cornerAt213_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 213 .north = false := rfl
theorem cornerAt213_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 213 .south = false := rfl
theorem cornerAt213_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 213 .east = false := rfl
theorem cornerAt213_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 213 .west = false := rfl
theorem cornerAt213_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 213 .northEast = (false && false) := rfl
theorem cornerAt213_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 213 .northWest = (false && false) := rfl
theorem cornerAt213_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 213 .southEast = (true && false) := rfl
theorem cornerAt213_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 213 .southWest = (true && false) := rfl
theorem cornerAt214_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 214 .north = false := rfl
theorem cornerAt214_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 214 .south = false := rfl
theorem cornerAt214_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 214 .east = false := rfl
theorem cornerAt214_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 214 .west = false := rfl
theorem cornerAt214_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 214 .northEast = (false && false) := rfl
theorem cornerAt214_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 214 .northWest = (false && false) := rfl
theorem cornerAt214_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 214 .southEast = (true && false) := rfl
theorem cornerAt214_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 214 .southWest = (true && false) := rfl
theorem cornerAt215_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 215 .north = false := rfl
theorem cornerAt215_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 215 .south = false := rfl
theorem cornerAt215_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 215 .east = false := rfl
theorem cornerAt215_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 215 .west = false := rfl
end NetHack.Soko22Hazard87
