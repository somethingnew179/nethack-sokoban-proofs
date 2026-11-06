import NetHack.Soko12Forward220.Unified.P00.OracleCorners01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P00
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem cornerAt161_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 161 .north = false := rfl
theorem cornerAt161_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 161 .south = false := rfl
theorem cornerAt161_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 161 .east = false := rfl
theorem cornerAt161_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 161 .west = false := rfl
theorem cornerAt161_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 161 .northEast = (p 135 && true) := rfl
theorem cornerAt161_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 161 .northWest = (p 135 && p 160) := rfl
theorem cornerAt161_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 161 .southEast = (p 187 && true) := rfl
theorem cornerAt161_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 161 .southWest = (p 187 && p 160) := rfl
theorem cornerAt163_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 163 .north = false := rfl
theorem cornerAt163_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 163 .south = false := rfl
theorem cornerAt163_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 163 .east = false := rfl
theorem cornerAt163_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 163 .west = false := rfl
theorem cornerAt163_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 163 .northEast = (true && p 164) := rfl
theorem cornerAt163_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 163 .northWest = (true && true) := rfl
theorem cornerAt163_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 163 .southEast = (p 189 && p 164) := rfl
theorem cornerAt163_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 163 .southWest = (p 189 && true) := rfl
theorem cornerAt164_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 164 .north = false := rfl
theorem cornerAt164_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 164 .south = false := rfl
theorem cornerAt164_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 164 .east = false := rfl
theorem cornerAt164_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 164 .west = false := rfl
theorem cornerAt164_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 164 .northEast = (true && true) := rfl
theorem cornerAt164_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 164 .northWest = (true && p 163) := rfl
theorem cornerAt164_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 164 .southEast = (p 190 && true) := rfl
theorem cornerAt164_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 164 .southWest = (p 190 && p 163) := rfl
theorem cornerAt166_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 166 .north = false := rfl
theorem cornerAt166_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 166 .south = false := rfl
theorem cornerAt166_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 166 .east = false := rfl
theorem cornerAt166_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 166 .west = false := rfl
theorem cornerAt166_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 166 .northEast = (p 140 && p 167) := rfl
theorem cornerAt166_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 166 .northWest = (p 140 && true) := rfl
theorem cornerAt166_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 166 .southEast = (p 192 && p 167) := rfl
theorem cornerAt166_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 166 .southWest = (p 192 && true) := rfl
theorem cornerAt167_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 167 .north = false := rfl
theorem cornerAt167_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 167 .south = false := rfl
theorem cornerAt167_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 167 .east = false := rfl
theorem cornerAt167_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 167 .west = false := rfl
theorem cornerAt167_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 167 .northEast = (p 141 && p 168) := rfl
theorem cornerAt167_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 167 .northWest = (p 141 && p 166) := rfl
theorem cornerAt167_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 167 .southEast = (p 193 && p 168) := rfl
theorem cornerAt167_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 167 .southWest = (p 193 && p 166) := rfl
theorem cornerAt168_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 168 .north = false := rfl
theorem cornerAt168_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 168 .south = false := rfl
theorem cornerAt168_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 168 .east = false := rfl
theorem cornerAt168_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 168 .west = false := rfl
theorem cornerAt168_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 168 .northEast = (p 142 && p 169) := rfl
theorem cornerAt168_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 168 .northWest = (p 142 && p 167) := rfl
theorem cornerAt168_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 168 .southEast = (p 194 && p 169) := rfl
theorem cornerAt168_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 168 .southWest = (p 194 && p 167) := rfl
theorem cornerAt169_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 169 .north = false := rfl
theorem cornerAt169_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 169 .south = false := rfl
theorem cornerAt169_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 169 .east = false := rfl
theorem cornerAt169_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 169 .west = false := rfl
theorem cornerAt169_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 169 .northEast = (p 143 && true) := rfl
theorem cornerAt169_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 169 .northWest = (p 143 && p 168) := rfl
theorem cornerAt169_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 169 .southEast = (true && true) := rfl
theorem cornerAt169_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 169 .southWest = (true && p 168) := rfl
theorem cornerAt184_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 184 .north = false := rfl
theorem cornerAt184_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 184 .south = false := rfl
theorem cornerAt184_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 184 .east = false := rfl
theorem cornerAt184_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 184 .west = false := rfl
theorem cornerAt184_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 184 .northEast = (p 158 && p 185) := rfl
theorem cornerAt184_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 184 .northWest = (p 158 && true) := rfl
theorem cornerAt184_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 184 .southEast = (p 210 && p 185) := rfl
theorem cornerAt184_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 184 .southWest = (p 210 && true) := rfl
theorem cornerAt185_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 185 .north = false := rfl
theorem cornerAt185_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 185 .south = false := rfl
theorem cornerAt185_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 185 .east = false := rfl
theorem cornerAt185_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 185 .west = false := rfl
theorem cornerAt185_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 185 .northEast = (p 159 && p 186) := rfl
theorem cornerAt185_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 185 .northWest = (p 159 && p 184) := rfl
theorem cornerAt185_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 185 .southEast = (p 211 && p 186) := rfl
theorem cornerAt185_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 185 .southWest = (p 211 && p 184) := rfl
theorem cornerAt186_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 186 .north = false := rfl
theorem cornerAt186_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 186 .south = false := rfl
theorem cornerAt186_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 186 .east = false := rfl
theorem cornerAt186_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 186 .west = false := rfl
theorem cornerAt186_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 186 .northEast = (p 160 && p 187) := rfl
theorem cornerAt186_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 186 .northWest = (p 160 && p 185) := rfl
theorem cornerAt186_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 186 .southEast = (p 212 && p 187) := rfl
theorem cornerAt186_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 186 .southWest = (p 212 && p 185) := rfl
theorem cornerAt187_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 187 .north = false := rfl
theorem cornerAt187_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 187 .south = false := rfl
theorem cornerAt187_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 187 .east = false := rfl
theorem cornerAt187_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 187 .west = false := rfl
theorem cornerAt187_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 187 .northEast = (p 161 && true) := rfl
theorem cornerAt187_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 187 .northWest = (p 161 && p 186) := rfl
theorem cornerAt187_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 187 .southEast = (p 213 && true) := rfl
theorem cornerAt187_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 187 .southWest = (p 213 && p 186) := rfl
theorem cornerAt189_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 189 .north = false := rfl
theorem cornerAt189_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 189 .south = false := rfl
theorem cornerAt189_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 189 .east = false := rfl
theorem cornerAt189_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 189 .west = false := rfl
theorem cornerAt189_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 189 .northEast = (p 163 && p 190) := rfl
theorem cornerAt189_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 189 .northWest = (p 163 && true) := rfl
theorem cornerAt189_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 189 .southEast = (p 215 && p 190) := rfl
theorem cornerAt189_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 189 .southWest = (p 215 && true) := rfl
theorem cornerAt190_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 190 .north = false := rfl
theorem cornerAt190_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 190 .south = false := rfl
theorem cornerAt190_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 190 .east = false := rfl
theorem cornerAt190_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) 190 .west = false := rfl
end NetHack.Soko12Forward220.Unified.P00
