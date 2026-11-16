import Owner1007.Guard188Eight11Data
namespace Owner1007.Guard188Eight11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem node3_north : FastCorral11.walkPart soko1_1.board locks region ⟨3,by decide⟩ .north=true := by decide +kernel
theorem node3_south : FastCorral11.walkPart soko1_1.board locks region ⟨3,by decide⟩ .south=true := by decide +kernel
theorem node3_east : FastCorral11.walkPart soko1_1.board locks region ⟨3,by decide⟩ .east=true := by decide +kernel
theorem node3_west : FastCorral11.walkPart soko1_1.board locks region ⟨3,by decide⟩ .west=true := by decide +kernel
theorem node3_northEast : FastCorral11.walkPart soko1_1.board locks region ⟨3,by decide⟩ .northEast=true := by decide +kernel
theorem node3_northWest : FastCorral11.walkPart soko1_1.board locks region ⟨3,by decide⟩ .northWest=true := by decide +kernel
theorem node3_southEast : FastCorral11.walkPart soko1_1.board locks region ⟨3,by decide⟩ .southEast=true := by decide +kernel
theorem node3_southWest : FastCorral11.walkPart soko1_1.board locks region ⟨3,by decide⟩ .southWest=true := by decide +kernel
theorem node3_push : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes locks region paid ⟨3,by decide⟩=true := by decide +kernel

end Owner1007.Guard188Eight11
