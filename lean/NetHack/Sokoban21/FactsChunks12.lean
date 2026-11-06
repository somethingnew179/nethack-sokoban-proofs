/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.FactsChunks11
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
theorem fact96 : pushFacts (⟨82,102,62,62,.north,2,10,false,false⟩ : PushEdge) = true := by decide
theorem fact97 : pushFacts (⟨82,62,102,102,.south,0,10,false,false⟩ : PushEdge) = true := by decide
theorem fact98 : pushFacts (⟨87,107,67,67,.north,0,1,false,false⟩ : PushEdge) = true := by decide
theorem fact99 : pushFacts (⟨87,67,107,107,.south,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact100 : pushFacts (⟨88,108,68,68,.north,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact101 : pushFacts (⟨88,68,108,108,.south,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact102 : pushFacts (⟨90,110,70,70,.north,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact103 : pushFacts (⟨90,70,110,110,.south,1,1,false,false⟩ : PushEdge) = true := by decide
end NetHack.Sokoban21
