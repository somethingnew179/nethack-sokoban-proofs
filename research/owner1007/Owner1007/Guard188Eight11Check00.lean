import Owner1007.Guard188Eight11Data
namespace Owner1007.Guard188Eight11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem node0_north : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .north=true := by decide +kernel
theorem node0_south : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .south=true := by decide +kernel
theorem node0_east : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .east=true := by decide +kernel
theorem node0_west : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .west=true := by decide +kernel
theorem node0_northEast : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .northEast=true := by decide +kernel
theorem node0_northWest : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .northWest=true := by decide +kernel
theorem node0_southEast : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .southEast=true := by decide +kernel
theorem node0_southWest : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .southWest=true := by decide +kernel
theorem node0_push : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes locks region paid ⟨0,by decide⟩=true := by decide +kernel

end Owner1007.Guard188Eight11
