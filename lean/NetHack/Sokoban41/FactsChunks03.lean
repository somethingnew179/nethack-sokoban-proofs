/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.FactsChunks02
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban41
theorem fact75 : pushFacts (⟨39,25,53,53,.south,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact76 : pushFacts (⟨43,57,29,29,.north,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact77 : pushFacts (⟨43,29,57,57,.south,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact78 : pushFacts (⟨44,58,30,30,.north,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact79 : pushFacts (⟨44,43,45,45,.east,0,1,false,false⟩ : PushEdge) = true := by decide
theorem fact80 : pushFacts (⟨44,30,58,58,.south,1,1,false,true⟩ : PushEdge) = true := by decide
theorem fact81 : pushFacts (⟨44,45,43,43,.west,1,1,false,true⟩ : PushEdge) = true := by decide
theorem fact82 : pushFacts (⟨45,44,46,46,.east,0,2,false,false⟩ : PushEdge) = true := by decide
theorem fact83 : pushFacts (⟨45,46,44,44,.west,2,2,false,false⟩ : PushEdge) = true := by decide
theorem fact84 : pushFacts (⟨46,45,47,47,.east,0,3,false,false⟩ : PushEdge) = true := by decide
theorem fact85 : pushFacts (⟨46,47,45,45,.west,2,3,false,false⟩ : PushEdge) = true := by decide
theorem fact86 : pushFacts (⟨47,46,48,48,.east,0,4,false,false⟩ : PushEdge) = true := by decide
theorem fact87 : pushFacts (⟨47,48,46,46,.west,2,4,false,false⟩ : PushEdge) = true := by decide
theorem fact88 : pushFacts (⟨48,47,49,49,.east,0,5,false,false⟩ : PushEdge) = true := by decide
theorem fact89 : pushFacts (⟨48,49,47,47,.west,2,5,false,false⟩ : PushEdge) = true := by decide
theorem fact90 : pushFacts (⟨49,48,50,50,.east,0,6,false,false⟩ : PushEdge) = true := by decide
theorem fact91 : pushFacts (⟨49,50,48,48,.west,2,6,false,false⟩ : PushEdge) = true := by decide
theorem fact92 : pushFacts (⟨50,49,51,51,.east,0,7,false,false⟩ : PushEdge) = true := by decide
theorem fact93 : pushFacts (⟨50,51,49,49,.west,2,7,false,false⟩ : PushEdge) = true := by decide
theorem fact94 : pushFacts (⟨51,50,52,52,.east,0,8,false,false⟩ : PushEdge) = true := by decide
theorem fact95 : pushFacts (⟨51,52,50,50,.west,2,8,false,false⟩ : PushEdge) = true := by decide
theorem fact96 : pushFacts (⟨52,66,38,38,.north,2,9,false,false⟩ : PushEdge) = true := by decide
theorem fact97 : pushFacts (⟨52,51,53,53,.east,9,9,false,true⟩ : PushEdge) = true := by decide
theorem fact98 : pushFacts (⟨52,38,66,66,.south,0,9,false,false⟩ : PushEdge) = true := by decide
theorem fact99 : pushFacts (⟨52,53,51,51,.west,2,9,false,false⟩ : PushEdge) = true := by decide
end NetHack.Sokoban41
