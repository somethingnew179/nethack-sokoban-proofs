/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.FactsChunks00
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
theorem fact8 : pushFacts (⟨26,25,27,27,.east,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact9 : pushFacts (⟨26,27,25,25,.west,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact10 : pushFacts (⟨27,26,28,28,.east,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact11 : pushFacts (⟨27,28,26,26,.west,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact12 : pushFacts (⟨31,30,32,32,.east,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact13 : pushFacts (⟨31,32,30,30,.west,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact14 : pushFacts (⟨35,34,36,36,.east,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact15 : pushFacts (⟨35,36,34,34,.west,1,1,true,true⟩ : PushEdge) = true := by decide
end NetHack.Sokoban21
