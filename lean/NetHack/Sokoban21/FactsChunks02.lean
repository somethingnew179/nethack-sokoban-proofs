/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.FactsChunks01
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
theorem fact16 : pushFacts (⟨36,35,37,37,.east,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact17 : pushFacts (⟨36,37,35,35,.west,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact18 : pushFacts (⟨37,36,38,38,.east,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact19 : pushFacts (⟨37,38,36,36,.west,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact20 : pushFacts (⟨41,61,21,21,.north,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact21 : pushFacts (⟨41,21,61,61,.south,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact22 : pushFacts (⟨42,62,22,22,.north,8,8,false,true⟩ : PushEdge) = true := by decide
theorem fact23 : pushFacts (⟨42,41,43,43,.east,2,8,false,false⟩ : PushEdge) = true := by decide
end NetHack.Sokoban21
