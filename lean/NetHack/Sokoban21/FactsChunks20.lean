/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.FactsChunks19
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
theorem fact160 : pushFacts (⟨122,102,142,142,.south,0,12,false,false⟩ : PushEdge) = true := by decide
theorem fact161 : pushFacts (⟨122,123,121,121,.west,12,12,false,true⟩ : PushEdge) = true := by decide
theorem fact162 : pushFacts (⟨123,143,103,103,.north,13,13,false,true⟩ : PushEdge) = true := by decide
theorem fact163 : pushFacts (⟨123,103,143,143,.south,0,13,false,false⟩ : PushEdge) = true := by decide
theorem fact164 : pushFacts (⟨126,146,106,106,.north,16,16,false,true⟩ : PushEdge) = true := by decide
theorem fact165 : pushFacts (⟨126,125,127,127,.east,16,16,false,true⟩ : PushEdge) = true := by decide
theorem fact166 : pushFacts (⟨126,106,146,146,.south,0,16,false,false⟩ : PushEdge) = true := by decide
theorem fact167 : pushFacts (⟨126,127,125,125,.west,16,16,false,true⟩ : PushEdge) = true := by decide
end NetHack.Sokoban21
