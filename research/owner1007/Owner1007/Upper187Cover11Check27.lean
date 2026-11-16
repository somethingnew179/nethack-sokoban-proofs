import Owner1007.Upper187Cover11Data
namespace Owner1007.Upper187Cover11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem node27_north : FastCorral11.walkPart soko1_1.board locks region ⟨27,by decide⟩ .north=true := by decide +kernel
theorem node27_south : FastCorral11.walkPart soko1_1.board locks region ⟨27,by decide⟩ .south=true := by decide +kernel
theorem node27_east : FastCorral11.walkPart soko1_1.board locks region ⟨27,by decide⟩ .east=true := by decide +kernel
theorem node27_west : FastCorral11.walkPart soko1_1.board locks region ⟨27,by decide⟩ .west=true := by decide +kernel
theorem node27_northEast : FastCorral11.walkPart soko1_1.board locks region ⟨27,by decide⟩ .northEast=true := by decide +kernel
theorem node27_northWest : FastCorral11.walkPart soko1_1.board locks region ⟨27,by decide⟩ .northWest=true := by decide +kernel
theorem node27_southEast : FastCorral11.walkPart soko1_1.board locks region ⟨27,by decide⟩ .southEast=true := by decide +kernel
theorem node27_southWest : FastCorral11.walkPart soko1_1.board locks region ⟨27,by decide⟩ .southWest=true := by decide +kernel
theorem node27_push : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes locks region paid ⟨27,by decide⟩=true := by decide +kernel

end Owner1007.Upper187Cover11
