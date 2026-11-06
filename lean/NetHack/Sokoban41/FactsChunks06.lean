/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.FactsChunks05
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban41
theorem fact150 : pushFacts (⟨120,106,134,134,.south,0,16,false,false⟩ : PushEdge) = true := by decide
theorem fact151 : pushFacts (⟨121,135,107,107,.north,2,15,false,false⟩ : PushEdge) = true := by decide
theorem fact152 : pushFacts (⟨121,120,122,122,.east,2,15,false,false⟩ : PushEdge) = true := by decide
theorem fact153 : pushFacts (⟨121,107,135,135,.south,0,15,false,false⟩ : PushEdge) = true := by decide
theorem fact154 : pushFacts (⟨121,122,120,120,.west,0,15,false,false⟩ : PushEdge) = true := by decide
theorem fact155 : pushFacts (⟨122,136,108,108,.north,2,14,false,false⟩ : PushEdge) = true := by decide
theorem fact156 : pushFacts (⟨122,121,123,123,.east,2,14,false,false⟩ : PushEdge) = true := by decide
theorem fact157 : pushFacts (⟨122,108,136,136,.south,0,14,false,false⟩ : PushEdge) = true := by decide
theorem fact158 : pushFacts (⟨122,123,121,121,.west,0,14,false,false⟩ : PushEdge) = true := by decide
theorem fact159 : pushFacts (⟨123,137,109,109,.north,2,13,false,false⟩ : PushEdge) = true := by decide
theorem fact160 : pushFacts (⟨123,122,124,124,.east,13,13,false,true⟩ : PushEdge) = true := by decide
theorem fact161 : pushFacts (⟨123,109,137,137,.south,0,13,false,false⟩ : PushEdge) = true := by decide
theorem fact162 : pushFacts (⟨123,124,122,122,.west,0,13,false,false⟩ : PushEdge) = true := by decide
theorem fact163 : pushFacts (⟨124,138,110,110,.north,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact164 : pushFacts (⟨124,110,138,138,.south,1,1,true,true⟩ : PushEdge) = true := by decide
end NetHack.Sokoban41
