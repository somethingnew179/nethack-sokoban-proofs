/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.FactsChunks32
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
theorem fact264 : pushFacts (⟨192,193,191,191,.west,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact265 : pushFacts (⟨193,192,194,194,.east,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact266 : pushFacts (⟨193,194,192,192,.west,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact267 : pushFacts (⟨194,193,195,195,.east,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact268 : pushFacts (⟨194,195,193,193,.west,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact269 : pushFacts (⟨195,194,196,196,.east,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact270 : pushFacts (⟨195,196,194,194,.west,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact271 : pushFacts (⟨196,195,197,197,.east,1,1,false,false⟩ : PushEdge) = true := by decide
end NetHack.Sokoban21
