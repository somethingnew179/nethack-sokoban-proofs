/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.FactsChunks06
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
theorem fact56 : pushFacts (⟨58,78,38,38,.north,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact57 : pushFacts (⟨58,38,78,78,.south,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact58 : pushFacts (⟨62,82,42,42,.north,2,9,false,false⟩ : PushEdge) = true := by decide
theorem fact59 : pushFacts (⟨62,42,82,82,.south,0,9,false,false⟩ : PushEdge) = true := by decide
theorem fact60 : pushFacts (⟨64,84,44,44,.north,0,5,false,false⟩ : PushEdge) = true := by decide
theorem fact61 : pushFacts (⟨64,44,84,84,.south,5,5,false,true⟩ : PushEdge) = true := by decide
theorem fact62 : pushFacts (⟨65,85,45,45,.north,2,4,false,false⟩ : PushEdge) = true := by decide
theorem fact63 : pushFacts (⟨65,64,66,66,.east,2,4,false,false⟩ : PushEdge) = true := by decide
end NetHack.Sokoban21
