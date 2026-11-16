import Owner1007.Fixed317Shaft11Data
namespace Owner1007.Fixed317Shaft11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem w3_0 : FastCorral11.walkPart soko1_1.board locks region ⟨3,by decide⟩ .north=true := by decide +kernel
theorem w3_1 : FastCorral11.walkPart soko1_1.board locks region ⟨3,by decide⟩ .south=true := by decide +kernel
theorem w3_2 : FastCorral11.walkPart soko1_1.board locks region ⟨3,by decide⟩ .east=true := by decide +kernel
theorem w3_3 : FastCorral11.walkPart soko1_1.board locks region ⟨3,by decide⟩ .west=true := by decide +kernel
theorem w3_4 : FastCorral11.walkPart soko1_1.board locks region ⟨3,by decide⟩ .northEast=true := by decide +kernel
theorem w3_5 : FastCorral11.walkPart soko1_1.board locks region ⟨3,by decide⟩ .northWest=true := by decide +kernel
theorem w3_6 : FastCorral11.walkPart soko1_1.board locks region ⟨3,by decide⟩ .southEast=true := by decide +kernel
theorem w3_7 : FastCorral11.walkPart soko1_1.board locks region ⟨3,by decide⟩ .southWest=true := by decide +kernel
theorem p3 : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes locks region paid ⟨3,by decide⟩=true := by decide +kernel
#print axioms p3
end Owner1007.Fixed317Shaft11
