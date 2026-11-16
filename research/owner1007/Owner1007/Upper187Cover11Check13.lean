import Owner1007.Upper187Cover11Data
namespace Owner1007.Upper187Cover11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem node13_north : FastCorral11.walkPart soko1_1.board locks region ⟨13,by decide⟩ .north=true := by decide +kernel
theorem node13_south : FastCorral11.walkPart soko1_1.board locks region ⟨13,by decide⟩ .south=true := by decide +kernel
theorem node13_east : FastCorral11.walkPart soko1_1.board locks region ⟨13,by decide⟩ .east=true := by decide +kernel
theorem node13_west : FastCorral11.walkPart soko1_1.board locks region ⟨13,by decide⟩ .west=true := by decide +kernel
theorem node13_northEast : FastCorral11.walkPart soko1_1.board locks region ⟨13,by decide⟩ .northEast=true := by decide +kernel
theorem node13_northWest : FastCorral11.walkPart soko1_1.board locks region ⟨13,by decide⟩ .northWest=true := by decide +kernel
theorem node13_southEast : FastCorral11.walkPart soko1_1.board locks region ⟨13,by decide⟩ .southEast=true := by decide +kernel
theorem node13_southWest : FastCorral11.walkPart soko1_1.board locks region ⟨13,by decide⟩ .southWest=true := by decide +kernel
theorem node13_push : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes locks region paid ⟨13,by decide⟩=true := by decide +kernel

end Owner1007.Upper187Cover11
