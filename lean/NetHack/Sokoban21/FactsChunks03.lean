/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.FactsChunks02
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
theorem fact24 : pushFacts (⟨42,22,62,62,.south,0,8,false,false⟩ : PushEdge) = true := by decide
theorem fact25 : pushFacts (⟨42,43,41,41,.west,8,8,false,true⟩ : PushEdge) = true := by decide
theorem fact26 : pushFacts (⟨43,42,44,44,.east,2,7,false,false⟩ : PushEdge) = true := by decide
theorem fact27 : pushFacts (⟨43,44,42,42,.west,0,7,false,false⟩ : PushEdge) = true := by decide
theorem fact28 : pushFacts (⟨44,64,24,24,.north,6,6,false,true⟩ : PushEdge) = true := by decide
theorem fact29 : pushFacts (⟨44,43,45,45,.east,4,6,false,false⟩ : PushEdge) = true := by decide
theorem fact30 : pushFacts (⟨44,24,64,64,.south,2,6,false,false⟩ : PushEdge) = true := by decide
theorem fact31 : pushFacts (⟨44,45,43,43,.west,0,6,false,false⟩ : PushEdge) = true := by decide
end NetHack.Sokoban21
