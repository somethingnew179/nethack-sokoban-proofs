/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.FactsChunks10
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
theorem fact88 : pushFacts (⟨76,56,96,96,.south,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact89 : pushFacts (⟨76,77,75,75,.west,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact90 : pushFacts (⟨77,97,57,57,.north,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact91 : pushFacts (⟨77,76,78,78,.east,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact92 : pushFacts (⟨77,57,97,97,.south,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact93 : pushFacts (⟨77,78,76,76,.west,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact94 : pushFacts (⟨78,98,58,58,.north,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact95 : pushFacts (⟨78,58,98,98,.south,1,1,true,true⟩ : PushEdge) = true := by decide
end NetHack.Sokoban21
