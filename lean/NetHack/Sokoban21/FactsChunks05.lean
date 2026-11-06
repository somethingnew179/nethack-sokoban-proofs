/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.FactsChunks04
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
theorem fact40 : pushFacts (⟨52,72,32,32,.north,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact41 : pushFacts (⟨52,32,72,72,.south,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact42 : pushFacts (⟨54,74,34,34,.north,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact43 : pushFacts (⟨54,34,74,74,.south,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact44 : pushFacts (⟨55,75,35,35,.north,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact45 : pushFacts (⟨55,54,56,56,.east,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact46 : pushFacts (⟨55,35,75,75,.south,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact47 : pushFacts (⟨55,56,54,54,.west,1,1,true,true⟩ : PushEdge) = true := by decide
end NetHack.Sokoban21
