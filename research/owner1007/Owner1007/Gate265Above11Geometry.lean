import Owner1007.Gate265Above11Data
namespace Owner1007.Gate265Above11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem w0_0 : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .north=true := by decide +kernel
theorem w1_0 : FastCorral11.walkPart soko1_1.board locks region ⟨1,by decide⟩ .north=true := by decide +kernel
theorem w0_1 : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .south=true := by decide +kernel
theorem w1_1 : FastCorral11.walkPart soko1_1.board locks region ⟨1,by decide⟩ .south=true := by decide +kernel
theorem w0_2 : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .east=true := by decide +kernel
theorem w1_2 : FastCorral11.walkPart soko1_1.board locks region ⟨1,by decide⟩ .east=true := by decide +kernel
theorem w0_3 : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .west=true := by decide +kernel
theorem w1_3 : FastCorral11.walkPart soko1_1.board locks region ⟨1,by decide⟩ .west=true := by decide +kernel
theorem w0_4 : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .northEast=true := by decide +kernel
theorem w1_4 : FastCorral11.walkPart soko1_1.board locks region ⟨1,by decide⟩ .northEast=true := by decide +kernel
theorem w0_5 : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .northWest=true := by decide +kernel
theorem w1_5 : FastCorral11.walkPart soko1_1.board locks region ⟨1,by decide⟩ .northWest=true := by decide +kernel
theorem w0_6 : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .southEast=true := by decide +kernel
theorem w1_6 : FastCorral11.walkPart soko1_1.board locks region ⟨1,by decide⟩ .southEast=true := by decide +kernel
theorem w0_7 : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .southWest=true := by decide +kernel
theorem w1_7 : FastCorral11.walkPart soko1_1.board locks region ⟨1,by decide⟩ .southWest=true := by decide +kernel
theorem p0 : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes locks region paid ⟨0,by decide⟩=true := by decide +kernel
theorem p1 : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes locks region paid ⟨1,by decide⟩=true := by decide +kernel
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid := by
 apply FastCorral11.closed_of_checks soko1_1.board soko1_1.initial.holes locks region paid ZeroWord11.reverse_checked floor
 intro i
 obtain ⟨i,bound⟩ := i
 have choices : i=0∨i=1 := by omega
 rcases choices with rfl|rfl
 ·apply FastCorral11.node_of_parts
  ·intro dir
   cases dir
   ·exact w0_0
   ·exact w0_1
   ·exact w0_2
   ·exact w0_3
   ·exact w0_4
   ·exact w0_5
   ·exact w0_6
   ·exact w0_7
  ·exact p0
 ·apply FastCorral11.node_of_parts
  ·intro dir
   cases dir
   ·exact w1_0
   ·exact w1_1
   ·exact w1_2
   ·exact w1_3
   ·exact w1_4
   ·exact w1_5
   ·exact w1_6
   ·exact w1_7
  ·exact p1
#print axioms closed
end Owner1007.Gate265Above11
