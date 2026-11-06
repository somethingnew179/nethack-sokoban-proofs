/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.FactsChunks20
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
theorem fact168 : pushFacts (⟨129,149,109,109,.north,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact169 : pushFacts (⟨129,109,149,149,.south,1,1,false,true⟩ : PushEdge) = true := by decide
theorem fact170 : pushFacts (⟨130,150,110,110,.north,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact171 : pushFacts (⟨130,129,131,131,.east,1,1,false,true⟩ : PushEdge) = true := by decide
theorem fact172 : pushFacts (⟨130,110,150,150,.south,1,1,false,true⟩ : PushEdge) = true := by decide
theorem fact173 : pushFacts (⟨130,131,129,129,.west,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact174 : pushFacts (⟨134,154,114,114,.north,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact175 : pushFacts (⟨134,114,154,154,.south,1,1,true,true⟩ : PushEdge) = true := by decide
end NetHack.Sokoban21
