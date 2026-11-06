/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.FactsChunks30
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
theorem fact248 : pushFacts (⟨188,187,189,189,.east,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact249 : pushFacts (⟨188,189,187,188,.west,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact250 : pushFacts (⟨188,189,187,187,.west,2,20,false,false⟩ : PushEdge) = true := by decide
theorem fact251 : pushFacts (⟨188,189,187,186,.west,2,20,false,false⟩ : PushEdge) = true := by decide
theorem fact252 : pushFacts (⟨188,189,187,185,.west,3,20,false,false⟩ : PushEdge) = true := by decide
theorem fact253 : pushFacts (⟨188,189,187,184,.west,4,20,false,false⟩ : PushEdge) = true := by decide
theorem fact254 : pushFacts (⟨188,189,187,183,.west,5,20,false,false⟩ : PushEdge) = true := by decide
theorem fact255 : pushFacts (⟨188,189,187,182,.west,6,20,false,false⟩ : PushEdge) = true := by decide
end NetHack.Sokoban21
