/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.FactsChunks24
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
theorem fact200 : pushFacts (⟨149,148,150,150,.east,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact201 : pushFacts (⟨149,150,148,148,.west,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact202 : pushFacts (⟨155,154,156,156,.east,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact203 : pushFacts (⟨155,156,154,154,.west,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact204 : pushFacts (⟨156,155,157,157,.east,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact205 : pushFacts (⟨156,157,155,155,.west,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact206 : pushFacts (⟨157,156,158,158,.east,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact207 : pushFacts (⟨157,158,156,156,.west,1,1,true,true⟩ : PushEdge) = true := by decide
end NetHack.Sokoban21
