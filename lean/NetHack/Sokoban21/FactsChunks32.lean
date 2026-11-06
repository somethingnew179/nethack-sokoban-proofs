/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.FactsChunks31
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
theorem fact256 : pushFacts (⟨188,189,187,181,.west,20,20,false,true⟩ : PushEdge) = true := by decide
theorem fact257 : pushFacts (⟨189,188,190,190,.east,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact258 : pushFacts (⟨189,190,188,188,.west,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact259 : pushFacts (⟨190,189,191,191,.east,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact260 : pushFacts (⟨190,191,189,189,.west,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact261 : pushFacts (⟨191,190,192,192,.east,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact262 : pushFacts (⟨191,192,190,190,.west,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact263 : pushFacts (⟨192,191,193,193,.east,1,1,false,false⟩ : PushEdge) = true := by decide
end NetHack.Sokoban21
