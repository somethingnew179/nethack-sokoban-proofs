import Owner1007.Upper187Cover11Data
namespace Owner1007.Upper187Cover11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem node28_north : FastCorral11.walkPart soko1_1.board locks region ⟨28,by decide⟩ .north=true := by decide +kernel
theorem node28_south : FastCorral11.walkPart soko1_1.board locks region ⟨28,by decide⟩ .south=true := by decide +kernel
theorem node28_east : FastCorral11.walkPart soko1_1.board locks region ⟨28,by decide⟩ .east=true := by decide +kernel
theorem node28_west : FastCorral11.walkPart soko1_1.board locks region ⟨28,by decide⟩ .west=true := by decide +kernel
theorem node28_northEast : FastCorral11.walkPart soko1_1.board locks region ⟨28,by decide⟩ .northEast=true := by decide +kernel
theorem node28_northWest : FastCorral11.walkPart soko1_1.board locks region ⟨28,by decide⟩ .northWest=true := by decide +kernel
theorem node28_southEast : FastCorral11.walkPart soko1_1.board locks region ⟨28,by decide⟩ .southEast=true := by decide +kernel
theorem node28_southWest : FastCorral11.walkPart soko1_1.board locks region ⟨28,by decide⟩ .southWest=true := by decide +kernel
theorem node28_push : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes locks region paid ⟨28,by decide⟩=true := by decide +kernel

end Owner1007.Upper187Cover11
