/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.FactsChunks09
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
theorem fact80 : pushFacts (⟨74,94,54,54,.north,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact81 : pushFacts (⟨74,54,94,94,.south,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact82 : pushFacts (⟨75,95,55,55,.north,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact83 : pushFacts (⟨75,74,76,76,.east,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact84 : pushFacts (⟨75,55,95,95,.south,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact85 : pushFacts (⟨75,76,74,74,.west,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact86 : pushFacts (⟨76,96,56,56,.north,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact87 : pushFacts (⟨76,75,77,77,.east,1,1,true,true⟩ : PushEdge) = true := by decide
end NetHack.Sokoban21
