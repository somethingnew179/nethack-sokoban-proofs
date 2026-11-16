import Owner1007.WestRank11Data
namespace Owner1007.WestRank11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem node14_north : FastCorral11.walkPart soko1_1.board locks region ⟨14,by decide⟩ .north=true := by decide +kernel
theorem node14_south : FastCorral11.walkPart soko1_1.board locks region ⟨14,by decide⟩ .south=true := by decide +kernel
theorem node14_east : FastCorral11.walkPart soko1_1.board locks region ⟨14,by decide⟩ .east=true := by decide +kernel
theorem node14_west : FastCorral11.walkPart soko1_1.board locks region ⟨14,by decide⟩ .west=true := by decide +kernel
theorem node14_northEast : FastCorral11.walkPart soko1_1.board locks region ⟨14,by decide⟩ .northEast=true := by decide +kernel
theorem node14_northWest : FastCorral11.walkPart soko1_1.board locks region ⟨14,by decide⟩ .northWest=true := by decide +kernel
theorem node14_southEast : FastCorral11.walkPart soko1_1.board locks region ⟨14,by decide⟩ .southEast=true := by decide +kernel
theorem node14_southWest : FastCorral11.walkPart soko1_1.board locks region ⟨14,by decide⟩ .southWest=true := by decide +kernel
theorem node14_push : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes locks region paid ⟨14,by decide⟩=true := by decide +kernel
theorem refine14 : refinementCheck ⟨14,by decide⟩=true := by decide +kernel
end Owner1007.WestRank11
