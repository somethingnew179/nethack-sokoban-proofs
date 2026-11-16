import Owner1007.CentralFirst11Data
import Owner1007.WestRankHead11
namespace Owner1007.CentralFirst11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem w0 : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .north=true := by decide +kernel
theorem w1 : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .south=true := by decide +kernel
theorem w2 : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .east=true := by decide +kernel
theorem w3 : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .west=true := by decide +kernel
theorem w4 : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .northEast=true := by decide +kernel
theorem w5 : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .northWest=true := by decide +kernel
theorem w6 : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .southEast=true := by decide +kernel
theorem w7 : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .southWest=true := by decide +kernel
theorem p : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes locks region paid ⟨0,by decide⟩=true := by
 apply List.all_eq_true.mpr
 intro source member
 apply List.all_eq_true.mpr
 intro dir _
 change (match advance soko1_1.board source dir.opposite with
   |none=>true
   |some hero=>decide (hero∉region 0 ∨BlockedPush soko1_1.board (locks 0) source dir ∨paid source dir ∨Corral11.Shift soko1_1.board soko1_1.initial.holes locks region 0 source dir))=true
 cases advance soko1_1.board source dir.opposite with
 |none=>rfl
 |some hero=>exact decide_eq_true (Or.inr (Or.inr (Or.inl member)))

#print axioms p
#print axioms w7
end Owner1007.CentralFirst11
