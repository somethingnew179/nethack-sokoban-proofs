import NetHack.Soko12Forward220.Unified.P02.OracleClears
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P02
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem cornerAt29_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 29 .north = false := rfl
theorem cornerAt29_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 29 .south = false := rfl
theorem cornerAt29_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 29 .east = false := rfl
theorem cornerAt29_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 29 .west = false := rfl
theorem cornerAt29_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 29 .northEast = (true && p 30) := rfl
theorem cornerAt29_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 29 .northWest = (true && true) := rfl
theorem cornerAt29_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 29 .southEast = (false && p 30) := rfl
theorem cornerAt29_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 29 .southWest = (false && true) := rfl
theorem cornerAt30_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 30 .north = false := rfl
theorem cornerAt30_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 30 .south = false := rfl
theorem cornerAt30_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 30 .east = false := rfl
theorem cornerAt30_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 30 .west = false := rfl
theorem cornerAt30_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 30 .northEast = (true && false) := rfl
theorem cornerAt30_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 30 .northWest = (true && p 29) := rfl
theorem cornerAt30_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 30 .southEast = (p 56 && false) := rfl
theorem cornerAt30_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 30 .southWest = (p 56 && p 29) := rfl
theorem cornerAt31_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 31 .north = false := rfl
theorem cornerAt31_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 31 .south = false := rfl
theorem cornerAt31_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 31 .east = false := rfl
theorem cornerAt31_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 31 .west = false := rfl
theorem cornerAt31_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 31 .northEast = (true && false) := rfl
theorem cornerAt31_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 31 .northWest = (true && p 30) := rfl
theorem cornerAt31_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 31 .southEast = (true && false) := rfl
theorem cornerAt31_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 31 .southWest = (true && p 30) := rfl
theorem cornerAt32_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 32 .north = false := rfl
theorem cornerAt32_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 32 .south = false := rfl
theorem cornerAt32_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 32 .east = false := rfl
theorem cornerAt32_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 32 .west = false := rfl
theorem cornerAt32_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 32 .northEast = (true && false) := rfl
theorem cornerAt32_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 32 .northWest = (true && false) := rfl
theorem cornerAt32_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 32 .southEast = (true && false) := rfl
theorem cornerAt32_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 32 .southWest = (true && false) := rfl
theorem cornerAt33_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 33 .north = false := rfl
theorem cornerAt33_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 33 .south = false := rfl
theorem cornerAt33_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 33 .east = false := rfl
theorem cornerAt33_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 33 .west = false := rfl
theorem cornerAt33_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 33 .northEast = (true && false) := rfl
theorem cornerAt33_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 33 .northWest = (true && false) := rfl
theorem cornerAt33_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 33 .southEast = (true && false) := rfl
theorem cornerAt33_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 33 .southWest = (true && false) := rfl
theorem cornerAt55_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 55 .north = false := rfl
theorem cornerAt55_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 55 .south = false := rfl
theorem cornerAt55_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 55 .east = false := rfl
theorem cornerAt55_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 55 .west = false := rfl
theorem cornerAt55_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 55 .northEast = (p 29 && p 56) := rfl
theorem cornerAt55_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 55 .northWest = (p 29 && true) := rfl
theorem cornerAt55_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 55 .southEast = (true && p 56) := rfl
theorem cornerAt55_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 55 .southWest = (true && true) := rfl
theorem cornerAt56_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 56 .north = false := rfl
theorem cornerAt56_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 56 .south = false := rfl
theorem cornerAt56_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 56 .east = false := rfl
theorem cornerAt56_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 56 .west = false := rfl
theorem cornerAt56_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 56 .northEast = (p 30 && true) := rfl
theorem cornerAt56_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 56 .northWest = (p 30 && false) := rfl
theorem cornerAt56_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 56 .southEast = (p 82 && true) := rfl
theorem cornerAt56_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 56 .southWest = (p 82 && false) := rfl
theorem cornerAt82_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 82 .north = false := rfl
theorem cornerAt82_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 82 .south = false := rfl
theorem cornerAt82_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 82 .east = false := rfl
theorem cornerAt82_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 82 .west = false := rfl
theorem cornerAt82_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 82 .northEast = (p 56 && true) := rfl
theorem cornerAt82_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 82 .northWest = (p 56 && true) := rfl
theorem cornerAt82_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 82 .southEast = (p 108 && true) := rfl
theorem cornerAt82_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 82 .southWest = (p 108 && true) := rfl
theorem cornerAt105_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 105 .north = false := rfl
theorem cornerAt105_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 105 .south = false := rfl
theorem cornerAt105_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 105 .east = false := rfl
theorem cornerAt105_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 105 .west = false := rfl
theorem cornerAt105_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 105 .northEast = (true && p 106) := rfl
theorem cornerAt105_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 105 .northWest = (true && true) := rfl
theorem cornerAt105_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 105 .southEast = (p 131 && p 106) := rfl
theorem cornerAt105_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 105 .southWest = (p 131 && true) := rfl
theorem cornerAt106_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 106 .north = false := rfl
theorem cornerAt106_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 106 .south = false := rfl
theorem cornerAt106_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 106 .east = false := rfl
theorem cornerAt106_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 106 .west = false := rfl
theorem cornerAt106_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 106 .northEast = (true && true) := rfl
theorem cornerAt106_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 106 .northWest = (true && p 105) := rfl
theorem cornerAt106_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 106 .southEast = (p 132 && true) := rfl
theorem cornerAt106_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 106 .southWest = (p 132 && p 105) := rfl
theorem cornerAt108_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 108 .north = false := rfl
theorem cornerAt108_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 108 .south = false := rfl
theorem cornerAt108_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 108 .east = false := rfl
theorem cornerAt108_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 108 .west = false := rfl
theorem cornerAt108_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 108 .northEast = (p 82 && true) := rfl
theorem cornerAt108_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 108 .northWest = (p 82 && true) := rfl
theorem cornerAt108_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 108 .southEast = (p 134 && true) := rfl
theorem cornerAt108_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 108 .southWest = (p 134 && true) := rfl
theorem cornerAt115_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 115 .north = false := rfl
theorem cornerAt115_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 115 .south = false := rfl
theorem cornerAt115_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 115 .east = false := rfl
theorem cornerAt115_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 115 .west = false := rfl
theorem cornerAt115_northEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 115 .northEast = (true && p 116) := rfl
theorem cornerAt115_northWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 115 .northWest = (true && true) := rfl
theorem cornerAt115_southEast (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 115 .southEast = (p 141 && p 116) := rfl
theorem cornerAt115_southWest (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 115 .southWest = (p 141 && true) := rfl
theorem cornerAt116_north (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 116 .north = false := rfl
theorem cornerAt116_south (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 116 .south = false := rfl
theorem cornerAt116_east (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 116 .east = false := rfl
theorem cornerAt116_west (p : Pattern) : HazardPattern.corner soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) 116 .west = false := rfl
end NetHack.Soko12Forward220.Unified.P02
