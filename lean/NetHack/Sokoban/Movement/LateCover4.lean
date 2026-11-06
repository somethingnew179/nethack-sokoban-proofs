/- Tiny independent coverage leaves; checked with lean-M768-j1. -/
import NetHack.Sokoban.Movement.LateData
set_option maxRecDepth 100000
set_option maxHeartbeats 500000
namespace NetHack.Sokoban.Movement.Late.Cover4
theorem row0 : Bounded.successorsCovered soko4_2.board initial layer5 = true := by decide
theorem row1 : Bounded.successorsCovered soko4_2.board {player := 113, boulders := [127, 20, 51], holes := [31]} layer5 = true := by decide
theorem row2 : Bounded.successorsCovered soko4_2.board {player := 143, boulders := [127, 20, 51], holes := [31]} layer5 = true := by decide
theorem row3 : Bounded.successorsCovered soko4_2.board {player := 129, boulders := [127, 20, 51], holes := [31]} layer5 = true := by decide
theorem row4 : Bounded.successorsCovered soko4_2.board {player := 127, boulders := [121, 20, 51], holes := [31]} layer5 = true := by decide
theorem row5 : Bounded.successorsCovered soko4_2.board {player := 114, boulders := [127, 20, 51], holes := [31]} layer5 = true := by decide
theorem row6 : Bounded.successorsCovered soko4_2.board {player := 144, boulders := [127, 20, 51], holes := [31]} layer5 = true := by decide
theorem row7 : Bounded.successorsCovered soko4_2.board {player := 98, boulders := [127, 20, 51], holes := [31]} layer5 = true := by decide
theorem row8 : Bounded.successorsCovered soko4_2.board {player := 99, boulders := [127, 20, 51], holes := [31]} layer5 = true := by decide
theorem row9 : Bounded.successorsCovered soko4_2.board {player := 130, boulders := [127, 20, 51], holes := [31]} layer5 = true := by decide
theorem row10 : Bounded.successorsCovered soko4_2.board {player := 115, boulders := [127, 20, 51], holes := [31]} layer5 = true := by decide
theorem row11 : Bounded.successorsCovered soko4_2.board {player := 145, boulders := [127, 20, 51], holes := [31]} layer5 = true := by decide
theorem row12 : Bounded.successorsCovered soko4_2.board {player := 128, boulders := [121, 20, 51], holes := [31]} layer5 = true := by decide
theorem row13 : Bounded.successorsCovered soko4_2.board {player := 126, boulders := [121, 20, 51], holes := [31]} layer5 = true := by decide
theorem row14 : Bounded.successorsCovered soko4_2.board {player := 113, boulders := [121, 20, 51], holes := [31]} layer5 = true := by decide
theorem row15 : Bounded.successorsCovered soko4_2.board {player := 143, boulders := [121, 20, 51], holes := [31]} layer5 = true := by decide
theorem row16 : Bounded.successorsCovered soko4_2.board {player := 100, boulders := [127, 20, 51], holes := [31]} layer5 = true := by decide
theorem row17 : Bounded.successorsCovered soko4_2.board {player := 84, boulders := [127, 20, 51], holes := [31]} layer5 = true := by decide
theorem row18 : Bounded.successorsCovered soko4_2.board {player := 131, boulders := [127, 20, 51], holes := [31]} layer5 = true := by decide
theorem row19 : Bounded.successorsCovered soko4_2.board {player := 116, boulders := [127, 20, 51], holes := [31]} layer5 = true := by decide
theorem row20 : Bounded.successorsCovered soko4_2.board {player := 146, boulders := [127, 20, 51], holes := [31]} layer5 = true := by decide
theorem row21 : Bounded.successorsCovered soko4_2.board {player := 101, boulders := [127, 20, 51], holes := [31]} layer5 = true := by decide
theorem row22 : Bounded.successorsCovered soko4_2.board {player := 129, boulders := [121, 20, 51], holes := [31]} layer5 = true := by decide
theorem row23 : Bounded.successorsCovered soko4_2.board {player := 114, boulders := [121, 20, 51], holes := [31]} layer5 = true := by decide
theorem row24 : Bounded.successorsCovered soko4_2.board {player := 144, boulders := [121, 20, 51], holes := [31]} layer5 = true := by decide
theorem row25 : Bounded.successorsCovered soko4_2.board {player := 125, boulders := [121, 20, 51], holes := [31]} layer5 = true := by decide
theorem row26 : Bounded.successorsCovered soko4_2.board {player := 98, boulders := [121, 20, 51], holes := [31]} layer5 = true := by decide
theorem row27 : Bounded.successorsCovered soko4_2.board {player := 99, boulders := [121, 20, 51], holes := [31]} layer5 = true := by decide
theorem row28 : Bounded.successorsCovered soko4_2.board {player := 69, boulders := [127, 20, 51], holes := [31]} layer5 = true := by decide
theorem row29 : Bounded.successorsCovered soko4_2.board {player := 70, boulders := [127, 20, 51], holes := [31]} layer5 = true := by decide
theorem row30 : Bounded.successorsCovered soko4_2.board {player := 132, boulders := [127, 20, 51], holes := [31]} layer5 = true := by decide
theorem row31 : Bounded.successorsCovered soko4_2.board {player := 117, boulders := [127, 20, 51], holes := [31]} layer5 = true := by decide
theorem row32 : Bounded.successorsCovered soko4_2.board {player := 147, boulders := [127, 20, 51], holes := [31]} layer5 = true := by decide
theorem row33 : Bounded.successorsCovered soko4_2.board {player := 102, boulders := [127, 20, 51], holes := [31]} layer5 = true := by decide
theorem row34 : Bounded.successorsCovered soko4_2.board {player := 130, boulders := [121, 20, 51], holes := [31]} layer5 = true := by decide
theorem row35 : Bounded.successorsCovered soko4_2.board {player := 115, boulders := [121, 20, 51], holes := [31]} layer5 = true := by decide
theorem row36 : Bounded.successorsCovered soko4_2.board {player := 145, boulders := [121, 20, 51], holes := [31]} layer5 = true := by decide
theorem row37 : Bounded.successorsCovered soko4_2.board {player := 100, boulders := [121, 20, 51], holes := [31]} layer5 = true := by decide
theorem row38 : Bounded.successorsCovered soko4_2.board {player := 124, boulders := [121, 20, 51], holes := [31]} layer5 = true := by decide
theorem row39 : Bounded.successorsCovered soko4_2.board {player := 84, boulders := [121, 20, 51], holes := [31]} layer5 = true := by decide

theorem covers : Bounded.covers soko4_2.board layer4 layer5 = true :=
  List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨row0, (List.forall_mem_cons.mpr ⟨row1, (List.forall_mem_cons.mpr ⟨row2, (List.forall_mem_cons.mpr ⟨row3, (List.forall_mem_cons.mpr ⟨row4, (List.forall_mem_cons.mpr ⟨row5, (List.forall_mem_cons.mpr ⟨row6, (List.forall_mem_cons.mpr ⟨row7, (List.forall_mem_cons.mpr ⟨row8, (List.forall_mem_cons.mpr ⟨row9, (List.forall_mem_cons.mpr ⟨row10, (List.forall_mem_cons.mpr ⟨row11, (List.forall_mem_cons.mpr ⟨row12, (List.forall_mem_cons.mpr ⟨row13, (List.forall_mem_cons.mpr ⟨row14, (List.forall_mem_cons.mpr ⟨row15, (List.forall_mem_cons.mpr ⟨row16, (List.forall_mem_cons.mpr ⟨row17, (List.forall_mem_cons.mpr ⟨row18, (List.forall_mem_cons.mpr ⟨row19, (List.forall_mem_cons.mpr ⟨row20, (List.forall_mem_cons.mpr ⟨row21, (List.forall_mem_cons.mpr ⟨row22, (List.forall_mem_cons.mpr ⟨row23, (List.forall_mem_cons.mpr ⟨row24, (List.forall_mem_cons.mpr ⟨row25, (List.forall_mem_cons.mpr ⟨row26, (List.forall_mem_cons.mpr ⟨row27, (List.forall_mem_cons.mpr ⟨row28, (List.forall_mem_cons.mpr ⟨row29, (List.forall_mem_cons.mpr ⟨row30, (List.forall_mem_cons.mpr ⟨row31, (List.forall_mem_cons.mpr ⟨row32, (List.forall_mem_cons.mpr ⟨row33, (List.forall_mem_cons.mpr ⟨row34, (List.forall_mem_cons.mpr ⟨row35, (List.forall_mem_cons.mpr ⟨row36, (List.forall_mem_cons.mpr ⟨row37, (List.forall_mem_cons.mpr ⟨row38, (List.forall_mem_cons.mpr ⟨row39, (by intro state member; cases member)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
end NetHack.Sokoban.Movement.Late.Cover4
