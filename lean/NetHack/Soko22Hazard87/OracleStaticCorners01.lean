import NetHack.Soko22Hazard87.OracleStaticCorners00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem cornerAt52_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 52 .northEast = (p 30 && true) := rfl
theorem cornerAt52_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 52 .northWest = (p 30 && p 51) := rfl
theorem cornerAt52_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 52 .southEast = (p 74 && true) := rfl
theorem cornerAt52_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 52 .southWest = (p 74 && p 51) := rfl
theorem cornerAt67_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 67 .north = false := rfl
theorem cornerAt67_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 67 .south = false := rfl
theorem cornerAt67_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 67 .east = false := rfl
theorem cornerAt67_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 67 .west = false := rfl
theorem cornerAt67_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 67 .northEast = (p 45 && true) := rfl
theorem cornerAt67_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 67 .northWest = (p 45 && true) := rfl
theorem cornerAt67_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 67 .southEast = (p 89 && true) := rfl
theorem cornerAt67_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 67 .southWest = (p 89 && true) := rfl
theorem cornerAt69_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 69 .north = false := rfl
theorem cornerAt69_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 69 .south = false := rfl
theorem cornerAt69_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 69 .east = false := rfl
theorem cornerAt69_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 69 .west = false := rfl
theorem cornerAt69_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 69 .northEast = (p 47 && p 70) := rfl
theorem cornerAt69_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 69 .northWest = (p 47 && true) := rfl
theorem cornerAt69_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 69 .southEast = (p 91 && p 70) := rfl
theorem cornerAt69_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 69 .southWest = (p 91 && true) := rfl
theorem cornerAt70_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 70 .north = false := rfl
theorem cornerAt70_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 70 .south = false := rfl
theorem cornerAt70_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 70 .east = false := rfl
theorem cornerAt70_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 70 .west = false := rfl
theorem cornerAt70_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 70 .northEast = (p 48 && p 71) := rfl
theorem cornerAt70_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 70 .northWest = (p 48 && p 69) := rfl
theorem cornerAt70_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 70 .southEast = (true && p 71) := rfl
theorem cornerAt70_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 70 .southWest = (true && p 69) := rfl
theorem cornerAt71_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 71 .north = false := rfl
theorem cornerAt71_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 71 .south = false := rfl
theorem cornerAt71_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 71 .east = false := rfl
theorem cornerAt71_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 71 .west = false := rfl
theorem cornerAt71_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 71 .northEast = (p 49 && true) := rfl
theorem cornerAt71_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 71 .northWest = (p 49 && p 70) := rfl
theorem cornerAt71_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 71 .southEast = (p 93 && true) := rfl
theorem cornerAt71_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 71 .southWest = (p 93 && p 70) := rfl
theorem cornerAt73_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 73 .north = false := rfl
theorem cornerAt73_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 73 .south = false := rfl
theorem cornerAt73_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 73 .east = false := rfl
theorem cornerAt73_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 73 .west = false := rfl
theorem cornerAt73_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 73 .northEast = (p 51 && p 74) := rfl
theorem cornerAt73_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 73 .northWest = (p 51 && true) := rfl
theorem cornerAt73_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 73 .southEast = (p 95 && p 74) := rfl
theorem cornerAt73_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 73 .southWest = (p 95 && true) := rfl
theorem cornerAt74_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 74 .north = false := rfl
theorem cornerAt74_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 74 .south = false := rfl
theorem cornerAt74_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 74 .east = false := rfl
theorem cornerAt74_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 74 .west = false := rfl
theorem cornerAt74_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 74 .northEast = (p 52 && true) := rfl
theorem cornerAt74_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 74 .northWest = (p 52 && p 73) := rfl
theorem cornerAt74_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 74 .southEast = (p 96 && true) := rfl
theorem cornerAt74_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 74 .southWest = (p 96 && p 73) := rfl
theorem cornerAt76_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 76 .north = false := rfl
theorem cornerAt76_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 76 .south = false := rfl
theorem cornerAt76_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 76 .east = false := rfl
theorem cornerAt76_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 76 .west = false := rfl
theorem cornerAt76_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 76 .northEast = (true && true) := rfl
theorem cornerAt76_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 76 .northWest = (true && true) := rfl
theorem cornerAt76_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 76 .southEast = (p 98 && true) := rfl
theorem cornerAt76_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 76 .southWest = (p 98 && true) := rfl
theorem cornerAt78_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 78 .north = false := rfl
theorem cornerAt78_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 78 .south = false := rfl
theorem cornerAt78_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 78 .east = false := rfl
theorem cornerAt78_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 78 .west = false := rfl
theorem cornerAt78_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 78 .northEast = (true && false) := rfl
theorem cornerAt78_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 78 .northWest = (true && true) := rfl
theorem cornerAt78_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 78 .southEast = (false && false) := rfl
theorem cornerAt78_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 78 .southWest = (false && true) := rfl
theorem cornerAt79_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 79 .north = false := rfl
theorem cornerAt79_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 79 .south = false := rfl
theorem cornerAt79_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 79 .east = false := rfl
theorem cornerAt79_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 79 .west = false := rfl
theorem cornerAt79_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 79 .northEast = (true && false) := rfl
theorem cornerAt79_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 79 .northWest = (true && false) := rfl
theorem cornerAt79_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 79 .southEast = (false && false) := rfl
theorem cornerAt79_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 79 .southWest = (false && false) := rfl
theorem cornerAt80_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 80 .north = false := rfl
theorem cornerAt80_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 80 .south = false := rfl
theorem cornerAt80_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 80 .east = false := rfl
theorem cornerAt80_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 80 .west = false := rfl
theorem cornerAt80_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 80 .northEast = (true && false) := rfl
theorem cornerAt80_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 80 .northWest = (true && false) := rfl
theorem cornerAt80_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 80 .southEast = (false && false) := rfl
theorem cornerAt80_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 80 .southWest = (false && false) := rfl
theorem cornerAt81_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 81 .north = false := rfl
theorem cornerAt81_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 81 .south = false := rfl
theorem cornerAt81_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 81 .east = false := rfl
theorem cornerAt81_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 81 .west = false := rfl
theorem cornerAt81_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 81 .northEast = (true && false) := rfl
theorem cornerAt81_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 81 .northWest = (true && false) := rfl
theorem cornerAt81_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 81 .southEast = (false && false) := rfl
theorem cornerAt81_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 81 .southWest = (false && false) := rfl
theorem cornerAt82_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 82 .north = false := rfl
theorem cornerAt82_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 82 .south = false := rfl
theorem cornerAt82_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 82 .east = false := rfl
theorem cornerAt82_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 82 .west = false := rfl
theorem cornerAt82_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 82 .northEast = (true && false) := rfl
theorem cornerAt82_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 82 .northWest = (true && false) := rfl
theorem cornerAt82_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 82 .southEast = (false && false) := rfl
theorem cornerAt82_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 82 .southWest = (false && false) := rfl
end NetHack.Soko22Hazard87
