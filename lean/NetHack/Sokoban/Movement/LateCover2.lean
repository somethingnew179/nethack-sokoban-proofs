/- Tiny independent coverage leaves; checked with lean-M768-j1. -/
import NetHack.Sokoban.Movement.LateData
set_option maxRecDepth 100000
set_option maxHeartbeats 500000
namespace NetHack.Sokoban.Movement.Late.Cover2
theorem row0 : Bounded.successorsCovered soko4_2.board initial layer3 = true := by decide
theorem row1 : Bounded.successorsCovered soko4_2.board {player := 113, boulders := [127, 20, 51], holes := [31]} layer3 = true := by decide
theorem row2 : Bounded.successorsCovered soko4_2.board {player := 143, boulders := [127, 20, 51], holes := [31]} layer3 = true := by decide
theorem row3 : Bounded.successorsCovered soko4_2.board {player := 129, boulders := [127, 20, 51], holes := [31]} layer3 = true := by decide
theorem row4 : Bounded.successorsCovered soko4_2.board {player := 127, boulders := [121, 20, 51], holes := [31]} layer3 = true := by decide
theorem row5 : Bounded.successorsCovered soko4_2.board {player := 114, boulders := [127, 20, 51], holes := [31]} layer3 = true := by decide
theorem row6 : Bounded.successorsCovered soko4_2.board {player := 144, boulders := [127, 20, 51], holes := [31]} layer3 = true := by decide
theorem row7 : Bounded.successorsCovered soko4_2.board {player := 98, boulders := [127, 20, 51], holes := [31]} layer3 = true := by decide
theorem row8 : Bounded.successorsCovered soko4_2.board {player := 99, boulders := [127, 20, 51], holes := [31]} layer3 = true := by decide
theorem row9 : Bounded.successorsCovered soko4_2.board {player := 130, boulders := [127, 20, 51], holes := [31]} layer3 = true := by decide
theorem row10 : Bounded.successorsCovered soko4_2.board {player := 115, boulders := [127, 20, 51], holes := [31]} layer3 = true := by decide
theorem row11 : Bounded.successorsCovered soko4_2.board {player := 145, boulders := [127, 20, 51], holes := [31]} layer3 = true := by decide
theorem row12 : Bounded.successorsCovered soko4_2.board {player := 128, boulders := [121, 20, 51], holes := [31]} layer3 = true := by decide
theorem row13 : Bounded.successorsCovered soko4_2.board {player := 126, boulders := [121, 20, 51], holes := [31]} layer3 = true := by decide
theorem row14 : Bounded.successorsCovered soko4_2.board {player := 113, boulders := [121, 20, 51], holes := [31]} layer3 = true := by decide
theorem row15 : Bounded.successorsCovered soko4_2.board {player := 143, boulders := [121, 20, 51], holes := [31]} layer3 = true := by decide
theorem row16 : Bounded.successorsCovered soko4_2.board {player := 100, boulders := [127, 20, 51], holes := [31]} layer3 = true := by decide

theorem covers : Bounded.covers soko4_2.board layer2 layer3 = true :=
  List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨row0, (List.forall_mem_cons.mpr ⟨row1, (List.forall_mem_cons.mpr ⟨row2, (List.forall_mem_cons.mpr ⟨row3, (List.forall_mem_cons.mpr ⟨row4, (List.forall_mem_cons.mpr ⟨row5, (List.forall_mem_cons.mpr ⟨row6, (List.forall_mem_cons.mpr ⟨row7, (List.forall_mem_cons.mpr ⟨row8, (List.forall_mem_cons.mpr ⟨row9, (List.forall_mem_cons.mpr ⟨row10, (List.forall_mem_cons.mpr ⟨row11, (List.forall_mem_cons.mpr ⟨row12, (List.forall_mem_cons.mpr ⟨row13, (List.forall_mem_cons.mpr ⟨row14, (List.forall_mem_cons.mpr ⟨row15, (List.forall_mem_cons.mpr ⟨row16, (by intro state member; cases member)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
end NetHack.Sokoban.Movement.Late.Cover2
