/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.FactsChunks29
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
theorem fact240 : pushFacts (⟨186,185,187,195,.east,0,0,false,false⟩ : PushEdge) = true := by decide
theorem fact241 : pushFacts (⟨186,185,187,196,.east,0,0,false,false⟩ : PushEdge) = true := by decide
theorem fact242 : pushFacts (⟨186,185,187,197,.east,0,0,false,false⟩ : PushEdge) = true := by decide
theorem fact243 : pushFacts (⟨186,185,187,198,.east,19,19,false,true⟩ : PushEdge) = true := by decide
theorem fact244 : pushFacts (⟨186,166,206,206,.south,19,19,false,true⟩ : PushEdge) = true := by decide
theorem fact245 : pushFacts (⟨186,187,185,185,.west,2,19,false,false⟩ : PushEdge) = true := by decide
theorem fact246 : pushFacts (⟨187,186,188,188,.east,0,0,false,false⟩ : PushEdge) = true := by decide
theorem fact247 : pushFacts (⟨187,188,186,186,.west,1,19,false,false⟩ : PushEdge) = true := by decide
end NetHack.Sokoban21
