/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.FactsChunks21
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
theorem fact176 : pushFacts (⟨135,155,115,115,.north,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact177 : pushFacts (⟨135,134,136,136,.east,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact178 : pushFacts (⟨135,115,155,155,.south,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact179 : pushFacts (⟨135,136,134,134,.west,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact180 : pushFacts (⟨136,156,116,116,.north,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact181 : pushFacts (⟨136,135,137,137,.east,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact182 : pushFacts (⟨136,116,156,156,.south,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact183 : pushFacts (⟨136,137,135,135,.west,1,1,true,true⟩ : PushEdge) = true := by decide
end NetHack.Sokoban21
