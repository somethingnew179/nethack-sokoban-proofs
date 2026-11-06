/- Tiny independent coverage leaves; checked with lean-M768-j1. -/
import NetHack.Sokoban.Movement.LateData
set_option maxRecDepth 100000
set_option maxHeartbeats 500000
namespace NetHack.Sokoban.Movement.Late.Cover0
theorem row0 : Bounded.successorsCovered soko4_2.board initial layer1 = true := by decide

theorem covers : Bounded.covers soko4_2.board layer0 layer1 = true :=
  List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨row0, (by intro state member; cases member)⟩)
end NetHack.Sokoban.Movement.Late.Cover0
