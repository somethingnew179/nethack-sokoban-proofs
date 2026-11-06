/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.FactsChunks03
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
theorem fact32 : pushFacts (⟨45,65,25,25,.north,3,3,false,true⟩ : PushEdge) = true := by decide
theorem fact33 : pushFacts (⟨45,25,65,65,.south,0,3,false,false⟩ : PushEdge) = true := by decide
theorem fact34 : pushFacts (⟨47,67,27,27,.north,1,1,false,true⟩ : PushEdge) = true := by decide
theorem fact35 : pushFacts (⟨47,27,67,67,.south,0,1,false,false⟩ : PushEdge) = true := by decide
theorem fact36 : pushFacts (⟨48,68,28,28,.north,1,1,false,true⟩ : PushEdge) = true := by decide
theorem fact37 : pushFacts (⟨48,28,68,68,.south,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact38 : pushFacts (⟨50,70,30,30,.north,1,1,false,true⟩ : PushEdge) = true := by decide
theorem fact39 : pushFacts (⟨50,30,70,70,.south,1,1,false,false⟩ : PushEdge) = true := by decide
end NetHack.Sokoban21
