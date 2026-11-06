/- Tiny independent coverage leaves; checked with lean-M768-j1. -/
import NetHack.Sokoban.Movement.LateData
set_option maxRecDepth 100000
set_option maxHeartbeats 500000
namespace NetHack.Sokoban.Movement.Late.Cover1
theorem row0 : Bounded.successorsCovered soko4_2.board initial layer2 = true := by decide
theorem row1 : Bounded.successorsCovered soko4_2.board {player := 113, boulders := [127, 20, 51], holes := [31]} layer2 = true := by decide
theorem row2 : Bounded.successorsCovered soko4_2.board {player := 143, boulders := [127, 20, 51], holes := [31]} layer2 = true := by decide
theorem row3 : Bounded.successorsCovered soko4_2.board {player := 129, boulders := [127, 20, 51], holes := [31]} layer2 = true := by decide
theorem row4 : Bounded.successorsCovered soko4_2.board {player := 127, boulders := [121, 20, 51], holes := [31]} layer2 = true := by decide
theorem row5 : Bounded.successorsCovered soko4_2.board {player := 114, boulders := [127, 20, 51], holes := [31]} layer2 = true := by decide
theorem row6 : Bounded.successorsCovered soko4_2.board {player := 144, boulders := [127, 20, 51], holes := [31]} layer2 = true := by decide

theorem covers : Bounded.covers soko4_2.board layer1 layer2 = true :=
  List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨row0, (List.forall_mem_cons.mpr ⟨row1, (List.forall_mem_cons.mpr ⟨row2, (List.forall_mem_cons.mpr ⟨row3, (List.forall_mem_cons.mpr ⟨row4, (List.forall_mem_cons.mpr ⟨row5, (List.forall_mem_cons.mpr ⟨row6, (by intro state member; cases member)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
end NetHack.Sokoban.Movement.Late.Cover1
