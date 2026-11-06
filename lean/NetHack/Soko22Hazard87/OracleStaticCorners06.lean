import NetHack.Soko22Hazard87.OracleStaticCorners05
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem cornerAt159_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 159 .north = false := rfl
theorem cornerAt159_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 159 .south = false := rfl
theorem cornerAt159_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 159 .east = false := rfl
theorem cornerAt159_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 159 .west = false := rfl
theorem cornerAt159_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 159 .northEast = (true && p 160) := rfl
theorem cornerAt159_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 159 .northWest = (true && p 158) := rfl
theorem cornerAt159_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 159 .southEast = (p 181 && p 160) := rfl
theorem cornerAt159_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 159 .southWest = (p 181 && p 158) := rfl
theorem cornerAt160_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 160 .north = false := rfl
theorem cornerAt160_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 160 .south = false := rfl
theorem cornerAt160_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 160 .east = false := rfl
theorem cornerAt160_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 160 .west = false := rfl
theorem cornerAt160_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 160 .northEast = (p 138 && p 161) := rfl
theorem cornerAt160_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 160 .northWest = (p 138 && p 159) := rfl
theorem cornerAt160_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 160 .southEast = (p 182 && p 161) := rfl
theorem cornerAt160_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 160 .southWest = (p 182 && p 159) := rfl
theorem cornerAt161_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 161 .north = false := rfl
theorem cornerAt161_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 161 .south = false := rfl
theorem cornerAt161_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 161 .east = false := rfl
theorem cornerAt161_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 161 .west = false := rfl
theorem cornerAt161_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 161 .northEast = (true && p 162) := rfl
theorem cornerAt161_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 161 .northWest = (true && p 160) := rfl
theorem cornerAt161_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 161 .southEast = (true && p 162) := rfl
theorem cornerAt161_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 161 .southWest = (true && p 160) := rfl
theorem cornerAt162_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 162 .north = false := rfl
theorem cornerAt162_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 162 .south = false := rfl
theorem cornerAt162_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 162 .east = false := rfl
theorem cornerAt162_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 162 .west = false := rfl
theorem cornerAt162_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 162 .northEast = (true && p 163) := rfl
theorem cornerAt162_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 162 .northWest = (true && p 161) := rfl
theorem cornerAt162_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 162 .southEast = (p 184 && p 163) := rfl
theorem cornerAt162_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 162 .southWest = (p 184 && p 161) := rfl
theorem cornerAt163_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 163 .north = false := rfl
theorem cornerAt163_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 163 .south = false := rfl
theorem cornerAt163_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 163 .east = false := rfl
theorem cornerAt163_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 163 .west = false := rfl
theorem cornerAt163_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 163 .northEast = (p 141 && p 164) := rfl
theorem cornerAt163_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 163 .northWest = (p 141 && p 162) := rfl
theorem cornerAt163_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 163 .southEast = (p 185 && p 164) := rfl
theorem cornerAt163_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 163 .southWest = (p 185 && p 162) := rfl
theorem cornerAt164_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 164 .north = false := rfl
theorem cornerAt164_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 164 .south = false := rfl
theorem cornerAt164_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 164 .east = false := rfl
theorem cornerAt164_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 164 .west = false := rfl
theorem cornerAt164_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 164 .northEast = (true && true) := rfl
theorem cornerAt164_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 164 .northWest = (true && p 163) := rfl
theorem cornerAt164_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 164 .southEast = (p 186 && true) := rfl
theorem cornerAt164_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 164 .southWest = (p 186 && p 163) := rfl
theorem cornerAt166_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 166 .north = false := rfl
theorem cornerAt166_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 166 .south = false := rfl
theorem cornerAt166_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 166 .east = false := rfl
theorem cornerAt166_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 166 .west = false := rfl
theorem cornerAt166_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 166 .northEast = (false && false) := rfl
theorem cornerAt166_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 166 .northWest = (false && true) := rfl
theorem cornerAt166_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 166 .southEast = (false && false) := rfl
theorem cornerAt166_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 166 .southWest = (false && true) := rfl
theorem cornerAt167_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 167 .north = false := rfl
theorem cornerAt167_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 167 .south = false := rfl
theorem cornerAt167_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 167 .east = false := rfl
theorem cornerAt167_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 167 .west = false := rfl
theorem cornerAt167_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 167 .northEast = (false && false) := rfl
theorem cornerAt167_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 167 .northWest = (false && false) := rfl
theorem cornerAt167_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 167 .southEast = (false && false) := rfl
theorem cornerAt167_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 167 .southWest = (false && false) := rfl
theorem cornerAt168_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 168 .north = false := rfl
theorem cornerAt168_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 168 .south = false := rfl
theorem cornerAt168_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 168 .east = false := rfl
theorem cornerAt168_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 168 .west = false := rfl
theorem cornerAt168_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 168 .northEast = (false && false) := rfl
theorem cornerAt168_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 168 .northWest = (false && false) := rfl
theorem cornerAt168_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 168 .southEast = (false && false) := rfl
theorem cornerAt168_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 168 .southWest = (false && false) := rfl
theorem cornerAt169_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 169 .north = false := rfl
theorem cornerAt169_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 169 .south = false := rfl
theorem cornerAt169_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 169 .east = false := rfl
theorem cornerAt169_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 169 .west = false := rfl
theorem cornerAt169_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 169 .northEast = (false && false) := rfl
theorem cornerAt169_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 169 .northWest = (false && false) := rfl
theorem cornerAt169_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 169 .southEast = (false && false) := rfl
theorem cornerAt169_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 169 .southWest = (false && false) := rfl
theorem cornerAt170_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 170 .north = false := rfl
theorem cornerAt170_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 170 .south = false := rfl
theorem cornerAt170_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 170 .east = false := rfl
theorem cornerAt170_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 170 .west = false := rfl
theorem cornerAt170_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 170 .northEast = (false && false) := rfl
theorem cornerAt170_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 170 .northWest = (false && false) := rfl
theorem cornerAt170_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 170 .southEast = (false && false) := rfl
theorem cornerAt170_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 170 .southWest = (false && false) := rfl
theorem cornerAt171_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 171 .north = false := rfl
theorem cornerAt171_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 171 .south = false := rfl
theorem cornerAt171_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 171 .east = false := rfl
theorem cornerAt171_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 171 .west = false := rfl
theorem cornerAt171_northEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 171 .northEast = (false && false) := rfl
theorem cornerAt171_northWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 171 .northWest = (false && false) := rfl
theorem cornerAt171_southEast (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 171 .southEast = (false && false) := rfl
theorem cornerAt171_southWest (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 171 .southWest = (false && false) := rfl
theorem cornerAt172_north (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 172 .north = false := rfl
theorem cornerAt172_south (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 172 .south = false := rfl
theorem cornerAt172_east (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 172 .east = false := rfl
theorem cornerAt172_west (p : Pattern) : HazardPattern.corner soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) 172 .west = false := rfl
end NetHack.Soko22Hazard87
