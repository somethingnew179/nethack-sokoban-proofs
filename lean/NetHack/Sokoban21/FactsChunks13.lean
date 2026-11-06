/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.FactsChunks12
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
theorem fact104 : pushFacts (⟨92,112,72,72,.north,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact105 : pushFacts (⟨92,72,112,112,.south,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact106 : pushFacts (⟨94,114,74,74,.north,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact107 : pushFacts (⟨94,74,114,114,.south,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact108 : pushFacts (⟨95,115,75,75,.north,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact109 : pushFacts (⟨95,94,96,96,.east,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact110 : pushFacts (⟨95,75,115,115,.south,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact111 : pushFacts (⟨95,96,94,94,.west,1,1,true,true⟩ : PushEdge) = true := by decide
end NetHack.Sokoban21
