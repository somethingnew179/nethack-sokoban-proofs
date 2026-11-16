import Owner1007.ParkedThree11Data
namespace Owner1007.ParkedThree11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem node1_north : FastCorral11.walkPart soko1_1.board locks region ⟨1,by decide⟩ .north=true := by decide +kernel
theorem node1_south : FastCorral11.walkPart soko1_1.board locks region ⟨1,by decide⟩ .south=true := by decide +kernel
theorem node1_east : FastCorral11.walkPart soko1_1.board locks region ⟨1,by decide⟩ .east=true := by decide +kernel
theorem node1_west : FastCorral11.walkPart soko1_1.board locks region ⟨1,by decide⟩ .west=true := by decide +kernel
theorem node1_northEast : FastCorral11.walkPart soko1_1.board locks region ⟨1,by decide⟩ .northEast=true := by decide +kernel
theorem node1_northWest : FastCorral11.walkPart soko1_1.board locks region ⟨1,by decide⟩ .northWest=true := by decide +kernel
theorem node1_southEast : FastCorral11.walkPart soko1_1.board locks region ⟨1,by decide⟩ .southEast=true := by decide +kernel
theorem node1_southWest : FastCorral11.walkPart soko1_1.board locks region ⟨1,by decide⟩ .southWest=true := by decide +kernel
theorem node1_push : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes locks region paid ⟨1,by decide⟩=true := by decide +kernel

end Owner1007.ParkedThree11
