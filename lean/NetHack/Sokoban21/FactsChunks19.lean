/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.FactsChunks18
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
theorem fact152 : pushFacts (⟨117,97,137,137,.south,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact153 : pushFacts (⟨117,118,116,116,.west,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact154 : pushFacts (⟨118,138,98,98,.north,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact155 : pushFacts (⟨118,98,138,138,.south,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact156 : pushFacts (⟨121,141,101,101,.north,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact157 : pushFacts (⟨121,101,141,141,.south,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact158 : pushFacts (⟨122,142,102,102,.north,2,12,false,false⟩ : PushEdge) = true := by decide
theorem fact159 : pushFacts (⟨122,121,123,123,.east,0,12,false,false⟩ : PushEdge) = true := by decide
end NetHack.Sokoban21
