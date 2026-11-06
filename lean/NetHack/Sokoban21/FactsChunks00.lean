/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.Rows
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
theorem fact0 : pushFacts (⟨22,21,23,23,.east,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact1 : pushFacts (⟨22,23,21,21,.west,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact2 : pushFacts (⟨23,22,24,24,.east,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact3 : pushFacts (⟨23,24,22,22,.west,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact4 : pushFacts (⟨24,23,25,25,.east,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact5 : pushFacts (⟨24,25,23,23,.west,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact6 : pushFacts (⟨25,24,26,26,.east,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact7 : pushFacts (⟨25,26,24,24,.west,1,1,true,true⟩ : PushEdge) = true := by decide
end NetHack.Sokoban21
