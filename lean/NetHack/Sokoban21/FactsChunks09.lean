/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.FactsChunks08
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
theorem fact72 : pushFacts (⟨68,88,48,48,.north,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact73 : pushFacts (⟨68,48,88,88,.south,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact74 : pushFacts (⟨70,90,50,50,.north,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact75 : pushFacts (⟨70,50,90,90,.south,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact76 : pushFacts (⟨71,70,72,72,.east,1,1,false,true⟩ : PushEdge) = true := by decide
theorem fact77 : pushFacts (⟨71,72,70,70,.west,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact78 : pushFacts (⟨72,92,52,52,.north,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact79 : pushFacts (⟨72,52,92,92,.south,1,1,true,true⟩ : PushEdge) = true := by decide
end NetHack.Sokoban21
