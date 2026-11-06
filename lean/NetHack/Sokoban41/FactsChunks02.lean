/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.FactsChunks01
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban41
theorem fact50 : pushFacts (⟨148,149,147,145,.west,0,0,false,false⟩ : PushEdge) = true := by decide
theorem fact51 : pushFacts (⟨148,149,147,144,.west,0,0,false,false⟩ : PushEdge) = true := by decide
theorem fact52 : pushFacts (⟨148,149,147,143,.west,0,0,false,false⟩ : PushEdge) = true := by decide
theorem fact53 : pushFacts (⟨148,149,147,142,.west,0,0,false,false⟩ : PushEdge) = true := by decide
theorem fact54 : pushFacts (⟨149,148,150,150,.east,2,17,false,false⟩ : PushEdge) = true := by decide
theorem fact55 : pushFacts (⟨149,150,148,148,.west,0,17,false,false⟩ : PushEdge) = true := by decide
theorem fact56 : pushFacts (⟨29,43,15,15,.north,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact57 : pushFacts (⟨29,15,43,43,.south,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact58 : pushFacts (⟨30,44,16,16,.north,1,1,false,true⟩ : PushEdge) = true := by decide
theorem fact59 : pushFacts (⟨30,29,31,31,.east,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact60 : pushFacts (⟨30,16,44,44,.south,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact61 : pushFacts (⟨30,31,29,29,.west,1,1,false,true⟩ : PushEdge) = true := by decide
theorem fact62 : pushFacts (⟨31,45,17,17,.north,1,1,false,true⟩ : PushEdge) = true := by decide
theorem fact63 : pushFacts (⟨31,30,32,32,.east,0,1,false,false⟩ : PushEdge) = true := by decide
theorem fact64 : pushFacts (⟨31,17,45,45,.south,0,1,false,false⟩ : PushEdge) = true := by decide
theorem fact65 : pushFacts (⟨31,32,30,30,.west,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact66 : pushFacts (⟨32,46,18,18,.north,2,2,false,true⟩ : PushEdge) = true := by decide
theorem fact67 : pushFacts (⟨32,18,46,46,.south,0,2,false,false⟩ : PushEdge) = true := by decide
theorem fact68 : pushFacts (⟨37,51,23,23,.north,7,7,false,true⟩ : PushEdge) = true := by decide
theorem fact69 : pushFacts (⟨37,23,51,51,.south,0,7,false,false⟩ : PushEdge) = true := by decide
theorem fact70 : pushFacts (⟨38,52,24,24,.north,8,8,false,true⟩ : PushEdge) = true := by decide
theorem fact71 : pushFacts (⟨38,37,39,39,.east,8,8,false,true⟩ : PushEdge) = true := by decide
theorem fact72 : pushFacts (⟨38,24,52,52,.south,0,8,false,false⟩ : PushEdge) = true := by decide
theorem fact73 : pushFacts (⟨38,39,37,37,.west,2,8,false,false⟩ : PushEdge) = true := by decide
theorem fact74 : pushFacts (⟨39,53,25,25,.north,1,1,true,true⟩ : PushEdge) = true := by decide
end NetHack.Sokoban41
