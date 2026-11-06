/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.FactsChunks23
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
theorem fact192 : pushFacts (⟨142,122,162,162,.south,0,13,false,false⟩ : PushEdge) = true := by decide
theorem fact193 : pushFacts (⟨142,143,141,141,.west,13,13,false,true⟩ : PushEdge) = true := by decide
theorem fact194 : pushFacts (⟨143,163,123,123,.north,2,14,false,false⟩ : PushEdge) = true := by decide
theorem fact195 : pushFacts (⟨143,123,163,163,.south,0,14,false,false⟩ : PushEdge) = true := by decide
theorem fact196 : pushFacts (⟨145,165,125,125,.north,16,16,false,true⟩ : PushEdge) = true := by decide
theorem fact197 : pushFacts (⟨145,125,165,165,.south,0,16,false,false⟩ : PushEdge) = true := by decide
theorem fact198 : pushFacts (⟨146,166,126,126,.north,2,17,false,false⟩ : PushEdge) = true := by decide
theorem fact199 : pushFacts (⟨146,126,166,166,.south,0,17,false,false⟩ : PushEdge) = true := by decide
end NetHack.Sokoban21
