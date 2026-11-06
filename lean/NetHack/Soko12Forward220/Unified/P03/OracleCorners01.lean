import NetHack.Soko12Forward220.Unified.P03.OracleCorners00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P03
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem cornerAt115_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 115 .northEast = (true && p 116) := rfl
theorem cornerAt115_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 115 .northWest = (true && true) := rfl
theorem cornerAt115_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 115 .southEast = (p 141 && p 116) := rfl
theorem cornerAt115_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 115 .southWest = (p 141 && true) := rfl
theorem cornerAt116_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 116 .north = false := rfl
theorem cornerAt116_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 116 .south = false := rfl
theorem cornerAt116_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 116 .east = false := rfl
theorem cornerAt116_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 116 .west = false := rfl
theorem cornerAt116_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 116 .northEast = (true && p 117) := rfl
theorem cornerAt116_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 116 .northWest = (true && p 115) := rfl
theorem cornerAt116_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 116 .southEast = (p 142 && p 117) := rfl
theorem cornerAt116_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 116 .southWest = (p 142 && p 115) := rfl
theorem cornerAt117_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 117 .north = false := rfl
theorem cornerAt117_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 117 .south = false := rfl
theorem cornerAt117_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 117 .east = false := rfl
theorem cornerAt117_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 117 .west = false := rfl
theorem cornerAt117_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 117 .northEast = (true && true) := rfl
theorem cornerAt117_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 117 .northWest = (true && p 116) := rfl
theorem cornerAt117_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 117 .southEast = (p 143 && true) := rfl
theorem cornerAt117_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 117 .southWest = (p 143 && p 116) := rfl
theorem cornerAt131_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 131 .north = false := rfl
theorem cornerAt131_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 131 .south = false := rfl
theorem cornerAt131_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 131 .east = false := rfl
theorem cornerAt131_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 131 .west = false := rfl
theorem cornerAt131_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 131 .northEast = (p 105 && p 132) := rfl
theorem cornerAt131_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 131 .northWest = (p 105 && true) := rfl
theorem cornerAt131_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 131 .southEast = (p 157 && p 132) := rfl
theorem cornerAt131_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 131 .southWest = (p 157 && true) := rfl
theorem cornerAt132_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 132 .north = false := rfl
theorem cornerAt132_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 132 .south = false := rfl
theorem cornerAt132_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 132 .east = false := rfl
theorem cornerAt132_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 132 .west = false := rfl
theorem cornerAt132_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 132 .northEast = (p 106 && p 133) := rfl
theorem cornerAt132_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 132 .northWest = (p 106 && p 131) := rfl
theorem cornerAt132_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 132 .southEast = (p 158 && p 133) := rfl
theorem cornerAt132_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 132 .southWest = (p 158 && p 131) := rfl
theorem cornerAt133_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 133 .north = false := rfl
theorem cornerAt133_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 133 .south = false := rfl
theorem cornerAt133_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 133 .east = false := rfl
theorem cornerAt133_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 133 .west = false := rfl
theorem cornerAt133_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 133 .northEast = (true && p 134) := rfl
theorem cornerAt133_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 133 .northWest = (true && p 132) := rfl
theorem cornerAt133_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 133 .southEast = (p 159 && p 134) := rfl
theorem cornerAt133_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 133 .southWest = (p 159 && p 132) := rfl
theorem cornerAt134_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 134 .north = false := rfl
theorem cornerAt134_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 134 .south = false := rfl
theorem cornerAt134_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 134 .east = false := rfl
theorem cornerAt134_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 134 .west = false := rfl
theorem cornerAt134_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 134 .northEast = (p 108 && p 135) := rfl
theorem cornerAt134_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 134 .northWest = (p 108 && p 133) := rfl
theorem cornerAt134_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 134 .southEast = (p 160 && p 135) := rfl
theorem cornerAt134_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 134 .southWest = (p 160 && p 133) := rfl
theorem cornerAt135_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 135 .north = false := rfl
theorem cornerAt135_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 135 .south = false := rfl
theorem cornerAt135_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 135 .east = false := rfl
theorem cornerAt135_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 135 .west = false := rfl
theorem cornerAt135_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 135 .northEast = (true && true) := rfl
theorem cornerAt135_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 135 .northWest = (true && p 134) := rfl
theorem cornerAt135_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 135 .southEast = (p 161 && true) := rfl
theorem cornerAt135_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 135 .southWest = (p 161 && p 134) := rfl
theorem cornerAt140_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 140 .north = false := rfl
theorem cornerAt140_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 140 .south = false := rfl
theorem cornerAt140_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 140 .east = false := rfl
theorem cornerAt140_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 140 .west = false := rfl
theorem cornerAt140_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 140 .northEast = (true && p 141) := rfl
theorem cornerAt140_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 140 .northWest = (true && true) := rfl
theorem cornerAt140_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 140 .southEast = (p 166 && p 141) := rfl
theorem cornerAt140_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 140 .southWest = (p 166 && true) := rfl
theorem cornerAt141_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 141 .north = false := rfl
theorem cornerAt141_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 141 .south = false := rfl
theorem cornerAt141_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 141 .east = false := rfl
theorem cornerAt141_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 141 .west = false := rfl
theorem cornerAt141_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 141 .northEast = (p 115 && p 142) := rfl
theorem cornerAt141_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 141 .northWest = (p 115 && p 140) := rfl
theorem cornerAt141_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 141 .southEast = (p 167 && p 142) := rfl
theorem cornerAt141_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 141 .southWest = (p 167 && p 140) := rfl
theorem cornerAt142_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 142 .north = false := rfl
theorem cornerAt142_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 142 .south = false := rfl
theorem cornerAt142_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 142 .east = false := rfl
theorem cornerAt142_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 142 .west = false := rfl
theorem cornerAt142_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 142 .northEast = (p 116 && p 143) := rfl
theorem cornerAt142_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 142 .northWest = (p 116 && p 141) := rfl
theorem cornerAt142_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 142 .southEast = (p 168 && p 143) := rfl
theorem cornerAt142_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 142 .southWest = (p 168 && p 141) := rfl
theorem cornerAt143_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 143 .north = false := rfl
theorem cornerAt143_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 143 .south = false := rfl
theorem cornerAt143_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 143 .east = false := rfl
theorem cornerAt143_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 143 .west = false := rfl
theorem cornerAt143_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 143 .northEast = (p 117 && true) := rfl
theorem cornerAt143_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 143 .northWest = (p 117 && p 142) := rfl
theorem cornerAt143_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 143 .southEast = (p 169 && true) := rfl
theorem cornerAt143_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 143 .southWest = (p 169 && p 142) := rfl
theorem cornerAt157_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 157 .north = false := rfl
theorem cornerAt157_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 157 .south = false := rfl
theorem cornerAt157_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 157 .east = false := rfl
theorem cornerAt157_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 157 .west = false := rfl
theorem cornerAt157_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 157 .northEast = (p 131 && p 158) := rfl
theorem cornerAt157_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 157 .northWest = (p 131 && true) := rfl
theorem cornerAt157_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 157 .southEast = (true && p 158) := rfl
theorem cornerAt157_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) 157 .southWest = (true && true) := rfl
end NetHack.Soko12Forward220.Unified.P03
