/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.FactsChunks33
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
theorem fact272 : pushFacts (⟨196,197,195,195,.west,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact273 : pushFacts (⟨197,196,198,198,.east,20,20,false,true⟩ : PushEdge) = true := by decide
theorem fact274 : pushFacts (⟨197,198,196,196,.west,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact275 : pushFacts (⟨202,201,203,203,.east,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact276 : pushFacts (⟨202,203,201,201,.west,1,1,true,true⟩ : PushEdge) = true := by decide
end NetHack.Sokoban21
