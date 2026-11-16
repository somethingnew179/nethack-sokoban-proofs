import Owner1007.Upper187Cover11Data
namespace Owner1007.Upper187Cover11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem node34_north : FastCorral11.walkPart soko1_1.board locks region ⟨34,by decide⟩ .north=true := by decide +kernel
theorem node34_south : FastCorral11.walkPart soko1_1.board locks region ⟨34,by decide⟩ .south=true := by decide +kernel
theorem node34_east : FastCorral11.walkPart soko1_1.board locks region ⟨34,by decide⟩ .east=true := by decide +kernel
theorem node34_west : FastCorral11.walkPart soko1_1.board locks region ⟨34,by decide⟩ .west=true := by decide +kernel
theorem node34_northEast : FastCorral11.walkPart soko1_1.board locks region ⟨34,by decide⟩ .northEast=true := by decide +kernel
theorem node34_northWest : FastCorral11.walkPart soko1_1.board locks region ⟨34,by decide⟩ .northWest=true := by decide +kernel
theorem node34_southEast : FastCorral11.walkPart soko1_1.board locks region ⟨34,by decide⟩ .southEast=true := by decide +kernel
theorem node34_southWest : FastCorral11.walkPart soko1_1.board locks region ⟨34,by decide⟩ .southWest=true := by decide +kernel
theorem node34_push : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes locks region paid ⟨34,by decide⟩=true := by decide +kernel

end Owner1007.Upper187Cover11
