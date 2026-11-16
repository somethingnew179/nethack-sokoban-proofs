import Owner1007.WestRank11Data
namespace Owner1007.WestRank11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem node8_north : FastCorral11.walkPart soko1_1.board locks region ⟨8,by decide⟩ .north=true := by decide +kernel
theorem node8_south : FastCorral11.walkPart soko1_1.board locks region ⟨8,by decide⟩ .south=true := by decide +kernel
theorem node8_east : FastCorral11.walkPart soko1_1.board locks region ⟨8,by decide⟩ .east=true := by decide +kernel
theorem node8_west : FastCorral11.walkPart soko1_1.board locks region ⟨8,by decide⟩ .west=true := by decide +kernel
theorem node8_northEast : FastCorral11.walkPart soko1_1.board locks region ⟨8,by decide⟩ .northEast=true := by decide +kernel
theorem node8_northWest : FastCorral11.walkPart soko1_1.board locks region ⟨8,by decide⟩ .northWest=true := by decide +kernel
theorem node8_southEast : FastCorral11.walkPart soko1_1.board locks region ⟨8,by decide⟩ .southEast=true := by decide +kernel
theorem node8_southWest : FastCorral11.walkPart soko1_1.board locks region ⟨8,by decide⟩ .southWest=true := by decide +kernel
theorem node8_push : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes locks region paid ⟨8,by decide⟩=true := by decide +kernel
theorem refine8 : refinementCheck ⟨8,by decide⟩=true := by decide +kernel
end Owner1007.WestRank11
