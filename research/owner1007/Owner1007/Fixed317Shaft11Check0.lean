import Owner1007.Fixed317Shaft11Data
namespace Owner1007.Fixed317Shaft11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem w0_0 : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .north=true := by decide +kernel
theorem w0_1 : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .south=true := by decide +kernel
theorem w0_2 : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .east=true := by decide +kernel
theorem w0_3 : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .west=true := by decide +kernel
theorem w0_4 : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .northEast=true := by decide +kernel
theorem w0_5 : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .northWest=true := by decide +kernel
theorem w0_6 : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .southEast=true := by decide +kernel
theorem w0_7 : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .southWest=true := by decide +kernel
theorem p0 : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes locks region paid ⟨0,by decide⟩=true := by decide +kernel
#print axioms p0
end Owner1007.Fixed317Shaft11
