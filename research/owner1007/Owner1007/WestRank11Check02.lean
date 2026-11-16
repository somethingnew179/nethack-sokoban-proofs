import Owner1007.WestRank11Data
namespace Owner1007.WestRank11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem node2_north : FastCorral11.walkPart soko1_1.board locks region ⟨2,by decide⟩ .north=true := by decide +kernel
theorem node2_south : FastCorral11.walkPart soko1_1.board locks region ⟨2,by decide⟩ .south=true := by decide +kernel
theorem node2_east : FastCorral11.walkPart soko1_1.board locks region ⟨2,by decide⟩ .east=true := by decide +kernel
theorem node2_west : FastCorral11.walkPart soko1_1.board locks region ⟨2,by decide⟩ .west=true := by decide +kernel
theorem node2_northEast : FastCorral11.walkPart soko1_1.board locks region ⟨2,by decide⟩ .northEast=true := by decide +kernel
theorem node2_northWest : FastCorral11.walkPart soko1_1.board locks region ⟨2,by decide⟩ .northWest=true := by decide +kernel
theorem node2_southEast : FastCorral11.walkPart soko1_1.board locks region ⟨2,by decide⟩ .southEast=true := by decide +kernel
theorem node2_southWest : FastCorral11.walkPart soko1_1.board locks region ⟨2,by decide⟩ .southWest=true := by decide +kernel
theorem node2_push : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes locks region paid ⟨2,by decide⟩=true := by decide +kernel
theorem refine2 : refinementCheck ⟨2,by decide⟩=true := by decide +kernel
end Owner1007.WestRank11
