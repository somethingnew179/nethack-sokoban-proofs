/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.FactsChunks28
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
theorem fact232 : pushFacts (⟨186,185,187,187,.east,1,19,false,false⟩ : PushEdge) = true := by decide
theorem fact233 : pushFacts (⟨186,185,187,188,.east,0,0,false,false⟩ : PushEdge) = true := by decide
theorem fact234 : pushFacts (⟨186,185,187,189,.east,0,0,false,false⟩ : PushEdge) = true := by decide
theorem fact235 : pushFacts (⟨186,185,187,190,.east,0,0,false,false⟩ : PushEdge) = true := by decide
theorem fact236 : pushFacts (⟨186,185,187,191,.east,0,0,false,false⟩ : PushEdge) = true := by decide
theorem fact237 : pushFacts (⟨186,185,187,192,.east,0,0,false,false⟩ : PushEdge) = true := by decide
theorem fact238 : pushFacts (⟨186,185,187,193,.east,0,0,false,false⟩ : PushEdge) = true := by decide
theorem fact239 : pushFacts (⟨186,185,187,194,.east,0,0,false,false⟩ : PushEdge) = true := by decide
end NetHack.Sokoban21
