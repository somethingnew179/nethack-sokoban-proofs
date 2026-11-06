import NetHack.Soko12Forward220.Unified.P03.OracleCells03
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P03
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem floorAt160 : soko1_2.board.floor.contains 160 = true := by decide +kernel
theorem doorAt160 : soko1_2.board.doors.contains 160 = false := by decide +kernel
theorem trapAt160 : soko1_2.board.rollingTraps.contains 160 = false := by decide +kernel
theorem boxAt160 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 160 = p 160 := rfl
theorem holeAt160 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 160 = false := rfl
theorem advanceAt160_north : advance soko1_2.board 160 .north = some 134 := by decide +kernel
theorem advanceAt160_south : advance soko1_2.board 160 .south = some 186 := by decide +kernel
theorem advanceAt160_east : advance soko1_2.board 160 .east = some 161 := by decide +kernel
theorem advanceAt160_west : advance soko1_2.board 160 .west = some 159 := by decide +kernel
theorem advanceAt160_northEast : advance soko1_2.board 160 .northEast = some 135 := by decide +kernel
theorem advanceAt160_northWest : advance soko1_2.board 160 .northWest = some 133 := by decide +kernel
theorem advanceAt160_southEast : advance soko1_2.board 160 .southEast = some 187 := by decide +kernel
theorem advanceAt160_southWest : advance soko1_2.board 160 .southWest = some 185 := by decide +kernel
theorem floorAt161 : soko1_2.board.floor.contains 161 = true := by decide +kernel
theorem doorAt161 : soko1_2.board.doors.contains 161 = false := by decide +kernel
theorem trapAt161 : soko1_2.board.rollingTraps.contains 161 = false := by decide +kernel
theorem boxAt161 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 161 = p 161 := rfl
theorem holeAt161 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 161 = false := rfl
theorem advanceAt161_north : advance soko1_2.board 161 .north = some 135 := by decide +kernel
theorem advanceAt161_south : advance soko1_2.board 161 .south = some 187 := by decide +kernel
theorem advanceAt161_east : advance soko1_2.board 161 .east = some 162 := by decide +kernel
theorem advanceAt161_west : advance soko1_2.board 161 .west = some 160 := by decide +kernel
theorem advanceAt161_northEast : advance soko1_2.board 161 .northEast = some 136 := by decide +kernel
theorem advanceAt161_northWest : advance soko1_2.board 161 .northWest = some 134 := by decide +kernel
theorem advanceAt161_southEast : advance soko1_2.board 161 .southEast = some 188 := by decide +kernel
theorem advanceAt161_southWest : advance soko1_2.board 161 .southWest = some 186 := by decide +kernel
theorem floorAt162 : soko1_2.board.floor.contains 162 = false := by decide +kernel
theorem doorAt162 : soko1_2.board.doors.contains 162 = false := by decide +kernel
theorem trapAt162 : soko1_2.board.rollingTraps.contains 162 = false := by decide +kernel
theorem boxAt162 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 162 = false := rfl
theorem holeAt162 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 162 = false := rfl
theorem advanceAt162_north : advance soko1_2.board 162 .north = some 136 := by decide +kernel
theorem advanceAt162_south : advance soko1_2.board 162 .south = some 188 := by decide +kernel
theorem advanceAt162_east : advance soko1_2.board 162 .east = some 163 := by decide +kernel
theorem advanceAt162_west : advance soko1_2.board 162 .west = some 161 := by decide +kernel
theorem advanceAt162_northEast : advance soko1_2.board 162 .northEast = some 137 := by decide +kernel
theorem advanceAt162_northWest : advance soko1_2.board 162 .northWest = some 135 := by decide +kernel
theorem advanceAt162_southEast : advance soko1_2.board 162 .southEast = some 189 := by decide +kernel
theorem advanceAt162_southWest : advance soko1_2.board 162 .southWest = some 187 := by decide +kernel
theorem floorAt163 : soko1_2.board.floor.contains 163 = true := by decide +kernel
theorem doorAt163 : soko1_2.board.doors.contains 163 = false := by decide +kernel
theorem trapAt163 : soko1_2.board.rollingTraps.contains 163 = false := by decide +kernel
theorem boxAt163 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 163 = p 163 := rfl
theorem holeAt163 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 163 = false := rfl
theorem advanceAt163_north : advance soko1_2.board 163 .north = some 137 := by decide +kernel
theorem advanceAt163_south : advance soko1_2.board 163 .south = some 189 := by decide +kernel
theorem advanceAt163_east : advance soko1_2.board 163 .east = some 164 := by decide +kernel
theorem advanceAt163_west : advance soko1_2.board 163 .west = some 162 := by decide +kernel
theorem advanceAt163_northEast : advance soko1_2.board 163 .northEast = some 138 := by decide +kernel
theorem advanceAt163_northWest : advance soko1_2.board 163 .northWest = some 136 := by decide +kernel
theorem advanceAt163_southEast : advance soko1_2.board 163 .southEast = some 190 := by decide +kernel
theorem advanceAt163_southWest : advance soko1_2.board 163 .southWest = some 188 := by decide +kernel
theorem floorAt164 : soko1_2.board.floor.contains 164 = true := by decide +kernel
theorem doorAt164 : soko1_2.board.doors.contains 164 = false := by decide +kernel
theorem trapAt164 : soko1_2.board.rollingTraps.contains 164 = false := by decide +kernel
theorem boxAt164 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 164 = p 164 := rfl
theorem holeAt164 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 164 = false := rfl
theorem advanceAt164_north : advance soko1_2.board 164 .north = some 138 := by decide +kernel
theorem advanceAt164_south : advance soko1_2.board 164 .south = some 190 := by decide +kernel
theorem advanceAt164_east : advance soko1_2.board 164 .east = some 165 := by decide +kernel
theorem advanceAt164_west : advance soko1_2.board 164 .west = some 163 := by decide +kernel
theorem advanceAt164_northEast : advance soko1_2.board 164 .northEast = some 139 := by decide +kernel
theorem advanceAt164_northWest : advance soko1_2.board 164 .northWest = some 137 := by decide +kernel
theorem advanceAt164_southEast : advance soko1_2.board 164 .southEast = some 191 := by decide +kernel
theorem advanceAt164_southWest : advance soko1_2.board 164 .southWest = some 189 := by decide +kernel
theorem floorAt165 : soko1_2.board.floor.contains 165 = false := by decide +kernel
theorem doorAt165 : soko1_2.board.doors.contains 165 = false := by decide +kernel
theorem trapAt165 : soko1_2.board.rollingTraps.contains 165 = false := by decide +kernel
theorem boxAt165 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 165 = false := rfl
theorem holeAt165 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 165 = false := rfl
theorem advanceAt165_north : advance soko1_2.board 165 .north = some 139 := by decide +kernel
theorem advanceAt165_south : advance soko1_2.board 165 .south = some 191 := by decide +kernel
theorem advanceAt165_east : advance soko1_2.board 165 .east = some 166 := by decide +kernel
theorem advanceAt165_west : advance soko1_2.board 165 .west = some 164 := by decide +kernel
theorem advanceAt165_northEast : advance soko1_2.board 165 .northEast = some 140 := by decide +kernel
theorem advanceAt165_northWest : advance soko1_2.board 165 .northWest = some 138 := by decide +kernel
theorem advanceAt165_southEast : advance soko1_2.board 165 .southEast = some 192 := by decide +kernel
theorem advanceAt165_southWest : advance soko1_2.board 165 .southWest = some 190 := by decide +kernel
theorem floorAt166 : soko1_2.board.floor.contains 166 = true := by decide +kernel
theorem doorAt166 : soko1_2.board.doors.contains 166 = false := by decide +kernel
theorem trapAt166 : soko1_2.board.rollingTraps.contains 166 = false := by decide +kernel
theorem boxAt166 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 166 = p 166 := rfl
theorem holeAt166 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 166 = false := rfl
theorem advanceAt166_north : advance soko1_2.board 166 .north = some 140 := by decide +kernel
theorem advanceAt166_south : advance soko1_2.board 166 .south = some 192 := by decide +kernel
theorem advanceAt166_east : advance soko1_2.board 166 .east = some 167 := by decide +kernel
theorem advanceAt166_west : advance soko1_2.board 166 .west = some 165 := by decide +kernel
theorem advanceAt166_northEast : advance soko1_2.board 166 .northEast = some 141 := by decide +kernel
theorem advanceAt166_northWest : advance soko1_2.board 166 .northWest = some 139 := by decide +kernel
theorem advanceAt166_southEast : advance soko1_2.board 166 .southEast = some 193 := by decide +kernel
theorem advanceAt166_southWest : advance soko1_2.board 166 .southWest = some 191 := by decide +kernel
theorem floorAt167 : soko1_2.board.floor.contains 167 = true := by decide +kernel
theorem doorAt167 : soko1_2.board.doors.contains 167 = false := by decide +kernel
theorem trapAt167 : soko1_2.board.rollingTraps.contains 167 = false := by decide +kernel
theorem boxAt167 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 167 = p 167 := rfl
theorem holeAt167 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 167 = false := rfl
theorem advanceAt167_north : advance soko1_2.board 167 .north = some 141 := by decide +kernel
theorem advanceAt167_south : advance soko1_2.board 167 .south = some 193 := by decide +kernel
theorem advanceAt167_east : advance soko1_2.board 167 .east = some 168 := by decide +kernel
theorem advanceAt167_west : advance soko1_2.board 167 .west = some 166 := by decide +kernel
theorem advanceAt167_northEast : advance soko1_2.board 167 .northEast = some 142 := by decide +kernel
theorem advanceAt167_northWest : advance soko1_2.board 167 .northWest = some 140 := by decide +kernel
theorem advanceAt167_southEast : advance soko1_2.board 167 .southEast = some 194 := by decide +kernel
theorem advanceAt167_southWest : advance soko1_2.board 167 .southWest = some 192 := by decide +kernel
theorem floorAt168 : soko1_2.board.floor.contains 168 = true := by decide +kernel
theorem doorAt168 : soko1_2.board.doors.contains 168 = false := by decide +kernel
theorem trapAt168 : soko1_2.board.rollingTraps.contains 168 = false := by decide +kernel
theorem boxAt168 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 168 = p 168 := rfl
theorem holeAt168 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 168 = false := rfl
theorem advanceAt168_north : advance soko1_2.board 168 .north = some 142 := by decide +kernel
theorem advanceAt168_south : advance soko1_2.board 168 .south = some 194 := by decide +kernel
theorem advanceAt168_east : advance soko1_2.board 168 .east = some 169 := by decide +kernel
theorem advanceAt168_west : advance soko1_2.board 168 .west = some 167 := by decide +kernel
theorem advanceAt168_northEast : advance soko1_2.board 168 .northEast = some 143 := by decide +kernel
theorem advanceAt168_northWest : advance soko1_2.board 168 .northWest = some 141 := by decide +kernel
theorem advanceAt168_southEast : advance soko1_2.board 168 .southEast = some 195 := by decide +kernel
theorem advanceAt168_southWest : advance soko1_2.board 168 .southWest = some 193 := by decide +kernel
theorem floorAt169 : soko1_2.board.floor.contains 169 = true := by decide +kernel
theorem doorAt169 : soko1_2.board.doors.contains 169 = false := by decide +kernel
theorem trapAt169 : soko1_2.board.rollingTraps.contains 169 = false := by decide +kernel
theorem boxAt169 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 169 = p 169 := rfl
theorem holeAt169 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 169 = false := rfl
theorem advanceAt169_north : advance soko1_2.board 169 .north = some 143 := by decide +kernel
theorem advanceAt169_south : advance soko1_2.board 169 .south = some 195 := by decide +kernel
theorem advanceAt169_east : advance soko1_2.board 169 .east = some 170 := by decide +kernel
theorem advanceAt169_west : advance soko1_2.board 169 .west = some 168 := by decide +kernel
theorem advanceAt169_northEast : advance soko1_2.board 169 .northEast = some 144 := by decide +kernel
theorem advanceAt169_northWest : advance soko1_2.board 169 .northWest = some 142 := by decide +kernel
theorem advanceAt169_southEast : advance soko1_2.board 169 .southEast = some 196 := by decide +kernel
theorem advanceAt169_southWest : advance soko1_2.board 169 .southWest = some 194 := by decide +kernel
theorem floorAt170 : soko1_2.board.floor.contains 170 = false := by decide +kernel
theorem doorAt170 : soko1_2.board.doors.contains 170 = false := by decide +kernel
theorem trapAt170 : soko1_2.board.rollingTraps.contains 170 = false := by decide +kernel
theorem boxAt170 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 170 = false := rfl
theorem holeAt170 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 170 = false := rfl
theorem advanceAt170_north : advance soko1_2.board 170 .north = some 144 := by decide +kernel
theorem advanceAt170_south : advance soko1_2.board 170 .south = some 196 := by decide +kernel
theorem advanceAt170_east : advance soko1_2.board 170 .east = some 171 := by decide +kernel
theorem advanceAt170_west : advance soko1_2.board 170 .west = some 169 := by decide +kernel
theorem advanceAt170_northEast : advance soko1_2.board 170 .northEast = some 145 := by decide +kernel
theorem advanceAt170_northWest : advance soko1_2.board 170 .northWest = some 143 := by decide +kernel
theorem advanceAt170_southEast : advance soko1_2.board 170 .southEast = some 197 := by decide +kernel
theorem advanceAt170_southWest : advance soko1_2.board 170 .southWest = some 195 := by decide +kernel
theorem floorAt171 : soko1_2.board.floor.contains 171 = false := by decide +kernel
theorem doorAt171 : soko1_2.board.doors.contains 171 = false := by decide +kernel
theorem trapAt171 : soko1_2.board.rollingTraps.contains 171 = false := by decide +kernel
theorem boxAt171 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 171 = false := rfl
theorem holeAt171 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 171 = false := rfl
theorem advanceAt171_north : advance soko1_2.board 171 .north = some 145 := by decide +kernel
theorem advanceAt171_south : advance soko1_2.board 171 .south = some 197 := by decide +kernel
theorem advanceAt171_east : advance soko1_2.board 171 .east = some 172 := by decide +kernel
theorem advanceAt171_west : advance soko1_2.board 171 .west = some 170 := by decide +kernel
theorem advanceAt171_northEast : advance soko1_2.board 171 .northEast = some 146 := by decide +kernel
theorem advanceAt171_northWest : advance soko1_2.board 171 .northWest = some 144 := by decide +kernel
theorem advanceAt171_southEast : advance soko1_2.board 171 .southEast = some 198 := by decide +kernel
theorem advanceAt171_southWest : advance soko1_2.board 171 .southWest = some 196 := by decide +kernel
theorem floorAt172 : soko1_2.board.floor.contains 172 = false := by decide +kernel
theorem doorAt172 : soko1_2.board.doors.contains 172 = false := by decide +kernel
theorem trapAt172 : soko1_2.board.rollingTraps.contains 172 = false := by decide +kernel
theorem boxAt172 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 172 = false := rfl
theorem holeAt172 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 172 = false := rfl
theorem advanceAt172_north : advance soko1_2.board 172 .north = some 146 := by decide +kernel
theorem advanceAt172_south : advance soko1_2.board 172 .south = some 198 := by decide +kernel
theorem advanceAt172_east : advance soko1_2.board 172 .east = some 173 := by decide +kernel
theorem advanceAt172_west : advance soko1_2.board 172 .west = some 171 := by decide +kernel
theorem advanceAt172_northEast : advance soko1_2.board 172 .northEast = some 147 := by decide +kernel
theorem advanceAt172_northWest : advance soko1_2.board 172 .northWest = some 145 := by decide +kernel
theorem advanceAt172_southEast : advance soko1_2.board 172 .southEast = some 199 := by decide +kernel
theorem advanceAt172_southWest : advance soko1_2.board 172 .southWest = some 197 := by decide +kernel
theorem floorAt173 : soko1_2.board.floor.contains 173 = false := by decide +kernel
theorem doorAt173 : soko1_2.board.doors.contains 173 = false := by decide +kernel
theorem trapAt173 : soko1_2.board.rollingTraps.contains 173 = false := by decide +kernel
theorem boxAt173 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 173 = false := rfl
theorem holeAt173 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 173 = false := rfl
theorem advanceAt173_north : advance soko1_2.board 173 .north = some 147 := by decide +kernel
theorem advanceAt173_south : advance soko1_2.board 173 .south = some 199 := by decide +kernel
theorem advanceAt173_east : advance soko1_2.board 173 .east = some 174 := by decide +kernel
theorem advanceAt173_west : advance soko1_2.board 173 .west = some 172 := by decide +kernel
theorem advanceAt173_northEast : advance soko1_2.board 173 .northEast = some 148 := by decide +kernel
theorem advanceAt173_northWest : advance soko1_2.board 173 .northWest = some 146 := by decide +kernel
theorem advanceAt173_southEast : advance soko1_2.board 173 .southEast = some 200 := by decide +kernel
theorem advanceAt173_southWest : advance soko1_2.board 173 .southWest = some 198 := by decide +kernel
theorem floorAt174 : soko1_2.board.floor.contains 174 = false := by decide +kernel
theorem doorAt174 : soko1_2.board.doors.contains 174 = false := by decide +kernel
theorem trapAt174 : soko1_2.board.rollingTraps.contains 174 = false := by decide +kernel
theorem boxAt174 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 174 = false := rfl
theorem holeAt174 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 174 = false := rfl
theorem advanceAt174_north : advance soko1_2.board 174 .north = some 148 := by decide +kernel
theorem advanceAt174_south : advance soko1_2.board 174 .south = some 200 := by decide +kernel
theorem advanceAt174_east : advance soko1_2.board 174 .east = some 175 := by decide +kernel
theorem advanceAt174_west : advance soko1_2.board 174 .west = some 173 := by decide +kernel
theorem advanceAt174_northEast : advance soko1_2.board 174 .northEast = some 149 := by decide +kernel
theorem advanceAt174_northWest : advance soko1_2.board 174 .northWest = some 147 := by decide +kernel
theorem advanceAt174_southEast : advance soko1_2.board 174 .southEast = some 201 := by decide +kernel
theorem advanceAt174_southWest : advance soko1_2.board 174 .southWest = some 199 := by decide +kernel
theorem floorAt175 : soko1_2.board.floor.contains 175 = false := by decide +kernel
theorem doorAt175 : soko1_2.board.doors.contains 175 = false := by decide +kernel
theorem trapAt175 : soko1_2.board.rollingTraps.contains 175 = false := by decide +kernel
theorem boxAt175 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 175 = false := rfl
theorem holeAt175 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 175 = false := rfl
theorem advanceAt175_north : advance soko1_2.board 175 .north = some 149 := by decide +kernel
theorem advanceAt175_south : advance soko1_2.board 175 .south = some 201 := by decide +kernel
theorem advanceAt175_east : advance soko1_2.board 175 .east = some 176 := by decide +kernel
theorem advanceAt175_west : advance soko1_2.board 175 .west = some 174 := by decide +kernel
theorem advanceAt175_northEast : advance soko1_2.board 175 .northEast = some 150 := by decide +kernel
theorem advanceAt175_northWest : advance soko1_2.board 175 .northWest = some 148 := by decide +kernel
theorem advanceAt175_southEast : advance soko1_2.board 175 .southEast = some 202 := by decide +kernel
theorem advanceAt175_southWest : advance soko1_2.board 175 .southWest = some 200 := by decide +kernel
theorem floorAt176 : soko1_2.board.floor.contains 176 = false := by decide +kernel
theorem doorAt176 : soko1_2.board.doors.contains 176 = false := by decide +kernel
theorem trapAt176 : soko1_2.board.rollingTraps.contains 176 = false := by decide +kernel
theorem boxAt176 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 176 = false := rfl
theorem holeAt176 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 176 = false := rfl
theorem advanceAt176_north : advance soko1_2.board 176 .north = some 150 := by decide +kernel
theorem advanceAt176_south : advance soko1_2.board 176 .south = some 202 := by decide +kernel
theorem advanceAt176_east : advance soko1_2.board 176 .east = some 177 := by decide +kernel
theorem advanceAt176_west : advance soko1_2.board 176 .west = some 175 := by decide +kernel
theorem advanceAt176_northEast : advance soko1_2.board 176 .northEast = some 151 := by decide +kernel
theorem advanceAt176_northWest : advance soko1_2.board 176 .northWest = some 149 := by decide +kernel
theorem advanceAt176_southEast : advance soko1_2.board 176 .southEast = some 203 := by decide +kernel
theorem advanceAt176_southWest : advance soko1_2.board 176 .southWest = some 201 := by decide +kernel
theorem floorAt177 : soko1_2.board.floor.contains 177 = false := by decide +kernel
theorem doorAt177 : soko1_2.board.doors.contains 177 = false := by decide +kernel
theorem trapAt177 : soko1_2.board.rollingTraps.contains 177 = false := by decide +kernel
theorem boxAt177 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 177 = false := rfl
theorem holeAt177 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 177 = false := rfl
theorem advanceAt177_north : advance soko1_2.board 177 .north = some 151 := by decide +kernel
theorem advanceAt177_south : advance soko1_2.board 177 .south = some 203 := by decide +kernel
theorem advanceAt177_east : advance soko1_2.board 177 .east = some 178 := by decide +kernel
theorem advanceAt177_west : advance soko1_2.board 177 .west = some 176 := by decide +kernel
theorem advanceAt177_northEast : advance soko1_2.board 177 .northEast = some 152 := by decide +kernel
theorem advanceAt177_northWest : advance soko1_2.board 177 .northWest = some 150 := by decide +kernel
theorem advanceAt177_southEast : advance soko1_2.board 177 .southEast = some 204 := by decide +kernel
theorem advanceAt177_southWest : advance soko1_2.board 177 .southWest = some 202 := by decide +kernel
theorem floorAt178 : soko1_2.board.floor.contains 178 = false := by decide +kernel
theorem doorAt178 : soko1_2.board.doors.contains 178 = false := by decide +kernel
theorem trapAt178 : soko1_2.board.rollingTraps.contains 178 = false := by decide +kernel
theorem boxAt178 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 178 = false := rfl
theorem holeAt178 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 178 = false := rfl
theorem advanceAt178_north : advance soko1_2.board 178 .north = some 152 := by decide +kernel
theorem advanceAt178_south : advance soko1_2.board 178 .south = some 204 := by decide +kernel
theorem advanceAt178_east : advance soko1_2.board 178 .east = some 179 := by decide +kernel
theorem advanceAt178_west : advance soko1_2.board 178 .west = some 177 := by decide +kernel
theorem advanceAt178_northEast : advance soko1_2.board 178 .northEast = some 153 := by decide +kernel
theorem advanceAt178_northWest : advance soko1_2.board 178 .northWest = some 151 := by decide +kernel
theorem advanceAt178_southEast : advance soko1_2.board 178 .southEast = some 205 := by decide +kernel
theorem advanceAt178_southWest : advance soko1_2.board 178 .southWest = some 203 := by decide +kernel
theorem floorAt179 : soko1_2.board.floor.contains 179 = false := by decide +kernel
theorem doorAt179 : soko1_2.board.doors.contains 179 = false := by decide +kernel
theorem trapAt179 : soko1_2.board.rollingTraps.contains 179 = false := by decide +kernel
theorem boxAt179 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 179 = false := rfl
theorem holeAt179 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 179 = false := rfl
theorem advanceAt179_north : advance soko1_2.board 179 .north = some 153 := by decide +kernel
theorem advanceAt179_south : advance soko1_2.board 179 .south = some 205 := by decide +kernel
theorem advanceAt179_east : advance soko1_2.board 179 .east = some 180 := by decide +kernel
theorem advanceAt179_west : advance soko1_2.board 179 .west = some 178 := by decide +kernel
theorem advanceAt179_northEast : advance soko1_2.board 179 .northEast = some 154 := by decide +kernel
theorem advanceAt179_northWest : advance soko1_2.board 179 .northWest = some 152 := by decide +kernel
theorem advanceAt179_southEast : advance soko1_2.board 179 .southEast = some 206 := by decide +kernel
theorem advanceAt179_southWest : advance soko1_2.board 179 .southWest = some 204 := by decide +kernel
theorem floorAt180 : soko1_2.board.floor.contains 180 = true := by decide +kernel
theorem doorAt180 : soko1_2.board.doors.contains 180 = false := by decide +kernel
theorem trapAt180 : soko1_2.board.rollingTraps.contains 180 = false := by decide +kernel
theorem boxAt180 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 180 = false := rfl
theorem holeAt180 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 180 = false := rfl
theorem advanceAt180_north : advance soko1_2.board 180 .north = some 154 := by decide +kernel
theorem advanceAt180_south : advance soko1_2.board 180 .south = some 206 := by decide +kernel
theorem advanceAt180_east : advance soko1_2.board 180 .east = some 181 := by decide +kernel
theorem advanceAt180_west : advance soko1_2.board 180 .west = some 179 := by decide +kernel
theorem advanceAt180_northEast : advance soko1_2.board 180 .northEast = some 155 := by decide +kernel
theorem advanceAt180_northWest : advance soko1_2.board 180 .northWest = some 153 := by decide +kernel
theorem advanceAt180_southEast : advance soko1_2.board 180 .southEast = some 207 := by decide +kernel
theorem advanceAt180_southWest : advance soko1_2.board 180 .southWest = some 205 := by decide +kernel
theorem floorAt181 : soko1_2.board.floor.contains 181 = false := by decide +kernel
theorem doorAt181 : soko1_2.board.doors.contains 181 = false := by decide +kernel
theorem trapAt181 : soko1_2.board.rollingTraps.contains 181 = false := by decide +kernel
theorem boxAt181 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 181 = false := rfl
theorem holeAt181 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 181 = false := rfl
theorem advanceAt181_north : advance soko1_2.board 181 .north = some 155 := by decide +kernel
theorem advanceAt181_south : advance soko1_2.board 181 .south = some 207 := by decide +kernel
theorem advanceAt181_east : advance soko1_2.board 181 .east = none := by decide +kernel
theorem advanceAt181_west : advance soko1_2.board 181 .west = some 180 := by decide +kernel
theorem advanceAt181_northEast : advance soko1_2.board 181 .northEast = none := by decide +kernel
theorem advanceAt181_northWest : advance soko1_2.board 181 .northWest = some 154 := by decide +kernel
theorem advanceAt181_southEast : advance soko1_2.board 181 .southEast = none := by decide +kernel
theorem advanceAt181_southWest : advance soko1_2.board 181 .southWest = some 206 := by decide +kernel
theorem floorAt182 : soko1_2.board.floor.contains 182 = false := by decide +kernel
theorem doorAt182 : soko1_2.board.doors.contains 182 = false := by decide +kernel
theorem trapAt182 : soko1_2.board.rollingTraps.contains 182 = false := by decide +kernel
theorem boxAt182 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 182 = false := rfl
theorem holeAt182 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 182 = false := rfl
theorem advanceAt182_north : advance soko1_2.board 182 .north = some 156 := by decide +kernel
theorem advanceAt182_south : advance soko1_2.board 182 .south = some 208 := by decide +kernel
theorem advanceAt182_east : advance soko1_2.board 182 .east = some 183 := by decide +kernel
theorem advanceAt182_west : advance soko1_2.board 182 .west = none := by decide +kernel
theorem advanceAt182_northEast : advance soko1_2.board 182 .northEast = some 157 := by decide +kernel
theorem advanceAt182_northWest : advance soko1_2.board 182 .northWest = none := by decide +kernel
theorem advanceAt182_southEast : advance soko1_2.board 182 .southEast = some 209 := by decide +kernel
theorem advanceAt182_southWest : advance soko1_2.board 182 .southWest = none := by decide +kernel
theorem floorAt183 : soko1_2.board.floor.contains 183 = false := by decide +kernel
theorem doorAt183 : soko1_2.board.doors.contains 183 = false := by decide +kernel
theorem trapAt183 : soko1_2.board.rollingTraps.contains 183 = false := by decide +kernel
theorem boxAt183 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 183 = false := rfl
theorem holeAt183 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 183 = false := rfl
theorem advanceAt183_north : advance soko1_2.board 183 .north = some 157 := by decide +kernel
theorem advanceAt183_south : advance soko1_2.board 183 .south = some 209 := by decide +kernel
theorem advanceAt183_east : advance soko1_2.board 183 .east = some 184 := by decide +kernel
theorem advanceAt183_west : advance soko1_2.board 183 .west = some 182 := by decide +kernel
theorem advanceAt183_northEast : advance soko1_2.board 183 .northEast = some 158 := by decide +kernel
theorem advanceAt183_northWest : advance soko1_2.board 183 .northWest = some 156 := by decide +kernel
theorem advanceAt183_southEast : advance soko1_2.board 183 .southEast = some 210 := by decide +kernel
theorem advanceAt183_southWest : advance soko1_2.board 183 .southWest = some 208 := by decide +kernel
theorem floorAt184 : soko1_2.board.floor.contains 184 = true := by decide +kernel
theorem doorAt184 : soko1_2.board.doors.contains 184 = false := by decide +kernel
theorem trapAt184 : soko1_2.board.rollingTraps.contains 184 = false := by decide +kernel
theorem boxAt184 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 184 = p 184 := rfl
theorem holeAt184 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 184 = false := rfl
theorem advanceAt184_north : advance soko1_2.board 184 .north = some 158 := by decide +kernel
theorem advanceAt184_south : advance soko1_2.board 184 .south = some 210 := by decide +kernel
theorem advanceAt184_east : advance soko1_2.board 184 .east = some 185 := by decide +kernel
theorem advanceAt184_west : advance soko1_2.board 184 .west = some 183 := by decide +kernel
theorem advanceAt184_northEast : advance soko1_2.board 184 .northEast = some 159 := by decide +kernel
theorem advanceAt184_northWest : advance soko1_2.board 184 .northWest = some 157 := by decide +kernel
theorem advanceAt184_southEast : advance soko1_2.board 184 .southEast = some 211 := by decide +kernel
theorem advanceAt184_southWest : advance soko1_2.board 184 .southWest = some 209 := by decide +kernel
theorem floorAt185 : soko1_2.board.floor.contains 185 = true := by decide +kernel
theorem doorAt185 : soko1_2.board.doors.contains 185 = false := by decide +kernel
theorem trapAt185 : soko1_2.board.rollingTraps.contains 185 = false := by decide +kernel
theorem boxAt185 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 185 = p 185 := rfl
theorem holeAt185 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 185 = false := rfl
theorem advanceAt185_north : advance soko1_2.board 185 .north = some 159 := by decide +kernel
theorem advanceAt185_south : advance soko1_2.board 185 .south = some 211 := by decide +kernel
theorem advanceAt185_east : advance soko1_2.board 185 .east = some 186 := by decide +kernel
theorem advanceAt185_west : advance soko1_2.board 185 .west = some 184 := by decide +kernel
theorem advanceAt185_northEast : advance soko1_2.board 185 .northEast = some 160 := by decide +kernel
theorem advanceAt185_northWest : advance soko1_2.board 185 .northWest = some 158 := by decide +kernel
theorem advanceAt185_southEast : advance soko1_2.board 185 .southEast = some 212 := by decide +kernel
theorem advanceAt185_southWest : advance soko1_2.board 185 .southWest = some 210 := by decide +kernel
theorem floorAt186 : soko1_2.board.floor.contains 186 = true := by decide +kernel
theorem doorAt186 : soko1_2.board.doors.contains 186 = false := by decide +kernel
theorem trapAt186 : soko1_2.board.rollingTraps.contains 186 = false := by decide +kernel
theorem boxAt186 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 186 = p 186 := rfl
theorem holeAt186 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 186 = false := rfl
theorem advanceAt186_north : advance soko1_2.board 186 .north = some 160 := by decide +kernel
theorem advanceAt186_south : advance soko1_2.board 186 .south = some 212 := by decide +kernel
theorem advanceAt186_east : advance soko1_2.board 186 .east = some 187 := by decide +kernel
theorem advanceAt186_west : advance soko1_2.board 186 .west = some 185 := by decide +kernel
theorem advanceAt186_northEast : advance soko1_2.board 186 .northEast = some 161 := by decide +kernel
theorem advanceAt186_northWest : advance soko1_2.board 186 .northWest = some 159 := by decide +kernel
theorem advanceAt186_southEast : advance soko1_2.board 186 .southEast = some 213 := by decide +kernel
theorem advanceAt186_southWest : advance soko1_2.board 186 .southWest = some 211 := by decide +kernel
theorem floorAt187 : soko1_2.board.floor.contains 187 = true := by decide +kernel
theorem doorAt187 : soko1_2.board.doors.contains 187 = false := by decide +kernel
theorem trapAt187 : soko1_2.board.rollingTraps.contains 187 = false := by decide +kernel
theorem boxAt187 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 187 = p 187 := rfl
theorem holeAt187 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 187 = false := rfl
theorem advanceAt187_north : advance soko1_2.board 187 .north = some 161 := by decide +kernel
theorem advanceAt187_south : advance soko1_2.board 187 .south = some 213 := by decide +kernel
theorem advanceAt187_east : advance soko1_2.board 187 .east = some 188 := by decide +kernel
theorem advanceAt187_west : advance soko1_2.board 187 .west = some 186 := by decide +kernel
theorem advanceAt187_northEast : advance soko1_2.board 187 .northEast = some 162 := by decide +kernel
theorem advanceAt187_northWest : advance soko1_2.board 187 .northWest = some 160 := by decide +kernel
theorem advanceAt187_southEast : advance soko1_2.board 187 .southEast = some 214 := by decide +kernel
theorem advanceAt187_southWest : advance soko1_2.board 187 .southWest = some 212 := by decide +kernel
theorem floorAt188 : soko1_2.board.floor.contains 188 = false := by decide +kernel
theorem doorAt188 : soko1_2.board.doors.contains 188 = false := by decide +kernel
theorem trapAt188 : soko1_2.board.rollingTraps.contains 188 = false := by decide +kernel
theorem boxAt188 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 188 = false := rfl
theorem holeAt188 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 188 = false := rfl
theorem advanceAt188_north : advance soko1_2.board 188 .north = some 162 := by decide +kernel
theorem advanceAt188_south : advance soko1_2.board 188 .south = some 214 := by decide +kernel
theorem advanceAt188_east : advance soko1_2.board 188 .east = some 189 := by decide +kernel
theorem advanceAt188_west : advance soko1_2.board 188 .west = some 187 := by decide +kernel
theorem advanceAt188_northEast : advance soko1_2.board 188 .northEast = some 163 := by decide +kernel
theorem advanceAt188_northWest : advance soko1_2.board 188 .northWest = some 161 := by decide +kernel
theorem advanceAt188_southEast : advance soko1_2.board 188 .southEast = some 215 := by decide +kernel
theorem advanceAt188_southWest : advance soko1_2.board 188 .southWest = some 213 := by decide +kernel
theorem floorAt189 : soko1_2.board.floor.contains 189 = true := by decide +kernel
theorem doorAt189 : soko1_2.board.doors.contains 189 = false := by decide +kernel
theorem trapAt189 : soko1_2.board.rollingTraps.contains 189 = false := by decide +kernel
theorem boxAt189 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 189 = p 189 := rfl
theorem holeAt189 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 189 = false := rfl
theorem advanceAt189_north : advance soko1_2.board 189 .north = some 163 := by decide +kernel
theorem advanceAt189_south : advance soko1_2.board 189 .south = some 215 := by decide +kernel
theorem advanceAt189_east : advance soko1_2.board 189 .east = some 190 := by decide +kernel
theorem advanceAt189_west : advance soko1_2.board 189 .west = some 188 := by decide +kernel
theorem advanceAt189_northEast : advance soko1_2.board 189 .northEast = some 164 := by decide +kernel
theorem advanceAt189_northWest : advance soko1_2.board 189 .northWest = some 162 := by decide +kernel
theorem advanceAt189_southEast : advance soko1_2.board 189 .southEast = some 216 := by decide +kernel
theorem advanceAt189_southWest : advance soko1_2.board 189 .southWest = some 214 := by decide +kernel
theorem floorAt190 : soko1_2.board.floor.contains 190 = true := by decide +kernel
theorem doorAt190 : soko1_2.board.doors.contains 190 = false := by decide +kernel
theorem trapAt190 : soko1_2.board.rollingTraps.contains 190 = false := by decide +kernel
theorem boxAt190 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 190 = p 190 := rfl
theorem holeAt190 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 190 = false := rfl
theorem advanceAt190_north : advance soko1_2.board 190 .north = some 164 := by decide +kernel
theorem advanceAt190_south : advance soko1_2.board 190 .south = some 216 := by decide +kernel
theorem advanceAt190_east : advance soko1_2.board 190 .east = some 191 := by decide +kernel
theorem advanceAt190_west : advance soko1_2.board 190 .west = some 189 := by decide +kernel
theorem advanceAt190_northEast : advance soko1_2.board 190 .northEast = some 165 := by decide +kernel
theorem advanceAt190_northWest : advance soko1_2.board 190 .northWest = some 163 := by decide +kernel
theorem advanceAt190_southEast : advance soko1_2.board 190 .southEast = some 217 := by decide +kernel
theorem advanceAt190_southWest : advance soko1_2.board 190 .southWest = some 215 := by decide +kernel
theorem floorAt191 : soko1_2.board.floor.contains 191 = true := by decide +kernel
theorem doorAt191 : soko1_2.board.doors.contains 191 = false := by decide +kernel
theorem trapAt191 : soko1_2.board.rollingTraps.contains 191 = false := by decide +kernel
theorem boxAt191 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 191 = p 191 := rfl
theorem holeAt191 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 191 = false := rfl
theorem advanceAt191_north : advance soko1_2.board 191 .north = some 165 := by decide +kernel
theorem advanceAt191_south : advance soko1_2.board 191 .south = some 217 := by decide +kernel
theorem advanceAt191_east : advance soko1_2.board 191 .east = some 192 := by decide +kernel
theorem advanceAt191_west : advance soko1_2.board 191 .west = some 190 := by decide +kernel
theorem advanceAt191_northEast : advance soko1_2.board 191 .northEast = some 166 := by decide +kernel
theorem advanceAt191_northWest : advance soko1_2.board 191 .northWest = some 164 := by decide +kernel
theorem advanceAt191_southEast : advance soko1_2.board 191 .southEast = some 218 := by decide +kernel
theorem advanceAt191_southWest : advance soko1_2.board 191 .southWest = some 216 := by decide +kernel
theorem floorAt192 : soko1_2.board.floor.contains 192 = true := by decide +kernel
theorem doorAt192 : soko1_2.board.doors.contains 192 = false := by decide +kernel
theorem trapAt192 : soko1_2.board.rollingTraps.contains 192 = false := by decide +kernel
theorem boxAt192 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 192 = p 192 := rfl
theorem holeAt192 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 192 = false := rfl
theorem advanceAt192_north : advance soko1_2.board 192 .north = some 166 := by decide +kernel
theorem advanceAt192_south : advance soko1_2.board 192 .south = some 218 := by decide +kernel
theorem advanceAt192_east : advance soko1_2.board 192 .east = some 193 := by decide +kernel
theorem advanceAt192_west : advance soko1_2.board 192 .west = some 191 := by decide +kernel
theorem advanceAt192_northEast : advance soko1_2.board 192 .northEast = some 167 := by decide +kernel
theorem advanceAt192_northWest : advance soko1_2.board 192 .northWest = some 165 := by decide +kernel
theorem advanceAt192_southEast : advance soko1_2.board 192 .southEast = some 219 := by decide +kernel
theorem advanceAt192_southWest : advance soko1_2.board 192 .southWest = some 217 := by decide +kernel
theorem floorAt193 : soko1_2.board.floor.contains 193 = true := by decide +kernel
theorem doorAt193 : soko1_2.board.doors.contains 193 = false := by decide +kernel
theorem trapAt193 : soko1_2.board.rollingTraps.contains 193 = false := by decide +kernel
theorem boxAt193 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 193 = p 193 := rfl
theorem holeAt193 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 193 = false := rfl
theorem advanceAt193_north : advance soko1_2.board 193 .north = some 167 := by decide +kernel
theorem advanceAt193_south : advance soko1_2.board 193 .south = some 219 := by decide +kernel
theorem advanceAt193_east : advance soko1_2.board 193 .east = some 194 := by decide +kernel
theorem advanceAt193_west : advance soko1_2.board 193 .west = some 192 := by decide +kernel
theorem advanceAt193_northEast : advance soko1_2.board 193 .northEast = some 168 := by decide +kernel
theorem advanceAt193_northWest : advance soko1_2.board 193 .northWest = some 166 := by decide +kernel
theorem advanceAt193_southEast : advance soko1_2.board 193 .southEast = some 220 := by decide +kernel
theorem advanceAt193_southWest : advance soko1_2.board 193 .southWest = some 218 := by decide +kernel
theorem floorAt194 : soko1_2.board.floor.contains 194 = true := by decide +kernel
theorem doorAt194 : soko1_2.board.doors.contains 194 = false := by decide +kernel
theorem trapAt194 : soko1_2.board.rollingTraps.contains 194 = false := by decide +kernel
theorem boxAt194 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 194 = p 194 := rfl
theorem holeAt194 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 194 = false := rfl
theorem advanceAt194_north : advance soko1_2.board 194 .north = some 168 := by decide +kernel
theorem advanceAt194_south : advance soko1_2.board 194 .south = some 220 := by decide +kernel
theorem advanceAt194_east : advance soko1_2.board 194 .east = some 195 := by decide +kernel
theorem advanceAt194_west : advance soko1_2.board 194 .west = some 193 := by decide +kernel
theorem advanceAt194_northEast : advance soko1_2.board 194 .northEast = some 169 := by decide +kernel
theorem advanceAt194_northWest : advance soko1_2.board 194 .northWest = some 167 := by decide +kernel
theorem advanceAt194_southEast : advance soko1_2.board 194 .southEast = some 221 := by decide +kernel
theorem advanceAt194_southWest : advance soko1_2.board 194 .southWest = some 219 := by decide +kernel
theorem floorAt195 : soko1_2.board.floor.contains 195 = false := by decide +kernel
theorem doorAt195 : soko1_2.board.doors.contains 195 = false := by decide +kernel
theorem trapAt195 : soko1_2.board.rollingTraps.contains 195 = false := by decide +kernel
theorem boxAt195 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 195 = false := rfl
theorem holeAt195 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 195 = false := rfl
theorem advanceAt195_north : advance soko1_2.board 195 .north = some 169 := by decide +kernel
theorem advanceAt195_south : advance soko1_2.board 195 .south = some 221 := by decide +kernel
theorem advanceAt195_east : advance soko1_2.board 195 .east = some 196 := by decide +kernel
theorem advanceAt195_west : advance soko1_2.board 195 .west = some 194 := by decide +kernel
theorem advanceAt195_northEast : advance soko1_2.board 195 .northEast = some 170 := by decide +kernel
theorem advanceAt195_northWest : advance soko1_2.board 195 .northWest = some 168 := by decide +kernel
theorem advanceAt195_southEast : advance soko1_2.board 195 .southEast = some 222 := by decide +kernel
theorem advanceAt195_southWest : advance soko1_2.board 195 .southWest = some 220 := by decide +kernel
theorem floorAt196 : soko1_2.board.floor.contains 196 = false := by decide +kernel
theorem doorAt196 : soko1_2.board.doors.contains 196 = false := by decide +kernel
theorem trapAt196 : soko1_2.board.rollingTraps.contains 196 = false := by decide +kernel
theorem boxAt196 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 196 = false := rfl
theorem holeAt196 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 196 = false := rfl
theorem advanceAt196_north : advance soko1_2.board 196 .north = some 170 := by decide +kernel
theorem advanceAt196_south : advance soko1_2.board 196 .south = some 222 := by decide +kernel
theorem advanceAt196_east : advance soko1_2.board 196 .east = some 197 := by decide +kernel
theorem advanceAt196_west : advance soko1_2.board 196 .west = some 195 := by decide +kernel
theorem advanceAt196_northEast : advance soko1_2.board 196 .northEast = some 171 := by decide +kernel
theorem advanceAt196_northWest : advance soko1_2.board 196 .northWest = some 169 := by decide +kernel
theorem advanceAt196_southEast : advance soko1_2.board 196 .southEast = some 223 := by decide +kernel
theorem advanceAt196_southWest : advance soko1_2.board 196 .southWest = some 221 := by decide +kernel
theorem floorAt197 : soko1_2.board.floor.contains 197 = false := by decide +kernel
theorem doorAt197 : soko1_2.board.doors.contains 197 = false := by decide +kernel
theorem trapAt197 : soko1_2.board.rollingTraps.contains 197 = false := by decide +kernel
theorem boxAt197 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 197 = false := rfl
theorem holeAt197 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 197 = false := rfl
theorem advanceAt197_north : advance soko1_2.board 197 .north = some 171 := by decide +kernel
theorem advanceAt197_south : advance soko1_2.board 197 .south = some 223 := by decide +kernel
theorem advanceAt197_east : advance soko1_2.board 197 .east = some 198 := by decide +kernel
theorem advanceAt197_west : advance soko1_2.board 197 .west = some 196 := by decide +kernel
theorem advanceAt197_northEast : advance soko1_2.board 197 .northEast = some 172 := by decide +kernel
theorem advanceAt197_northWest : advance soko1_2.board 197 .northWest = some 170 := by decide +kernel
theorem advanceAt197_southEast : advance soko1_2.board 197 .southEast = some 224 := by decide +kernel
theorem advanceAt197_southWest : advance soko1_2.board 197 .southWest = some 222 := by decide +kernel
theorem floorAt198 : soko1_2.board.floor.contains 198 = false := by decide +kernel
theorem doorAt198 : soko1_2.board.doors.contains 198 = false := by decide +kernel
theorem trapAt198 : soko1_2.board.rollingTraps.contains 198 = false := by decide +kernel
theorem boxAt198 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 198 = false := rfl
theorem holeAt198 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 198 = false := rfl
theorem advanceAt198_north : advance soko1_2.board 198 .north = some 172 := by decide +kernel
theorem advanceAt198_south : advance soko1_2.board 198 .south = some 224 := by decide +kernel
theorem advanceAt198_east : advance soko1_2.board 198 .east = some 199 := by decide +kernel
theorem advanceAt198_west : advance soko1_2.board 198 .west = some 197 := by decide +kernel
theorem advanceAt198_northEast : advance soko1_2.board 198 .northEast = some 173 := by decide +kernel
theorem advanceAt198_northWest : advance soko1_2.board 198 .northWest = some 171 := by decide +kernel
theorem advanceAt198_southEast : advance soko1_2.board 198 .southEast = some 225 := by decide +kernel
theorem advanceAt198_southWest : advance soko1_2.board 198 .southWest = some 223 := by decide +kernel
theorem floorAt199 : soko1_2.board.floor.contains 199 = false := by decide +kernel
theorem doorAt199 : soko1_2.board.doors.contains 199 = false := by decide +kernel
theorem trapAt199 : soko1_2.board.rollingTraps.contains 199 = false := by decide +kernel
theorem boxAt199 (p : Pattern) : HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p 199 = false := rfl
theorem holeAt199 (p : Pattern) : project (soko1_2.initial.holes.drop 3) 199 = false := rfl
theorem advanceAt199_north : advance soko1_2.board 199 .north = some 173 := by decide +kernel
theorem advanceAt199_south : advance soko1_2.board 199 .south = some 225 := by decide +kernel
theorem advanceAt199_east : advance soko1_2.board 199 .east = some 200 := by decide +kernel
theorem advanceAt199_west : advance soko1_2.board 199 .west = some 198 := by decide +kernel
theorem advanceAt199_northEast : advance soko1_2.board 199 .northEast = some 174 := by decide +kernel
theorem advanceAt199_northWest : advance soko1_2.board 199 .northWest = some 172 := by decide +kernel
theorem advanceAt199_southEast : advance soko1_2.board 199 .southEast = some 226 := by decide +kernel
theorem advanceAt199_southWest : advance soko1_2.board 199 .southWest = some 224 := by decide +kernel
end NetHack.Soko12Forward220.Unified.P03
