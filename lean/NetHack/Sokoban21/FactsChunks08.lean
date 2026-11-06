/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.FactsChunks07
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
theorem fact64 : pushFacts (⟨65,45,85,85,.south,4,4,false,true⟩ : PushEdge) = true := by decide
theorem fact65 : pushFacts (⟨65,66,64,64,.west,0,4,false,false⟩ : PushEdge) = true := by decide
theorem fact66 : pushFacts (⟨66,65,67,67,.east,2,3,false,false⟩ : PushEdge) = true := by decide
theorem fact67 : pushFacts (⟨66,67,65,65,.west,0,3,false,false⟩ : PushEdge) = true := by decide
theorem fact68 : pushFacts (⟨67,87,47,47,.north,2,2,false,false⟩ : PushEdge) = true := by decide
theorem fact69 : pushFacts (⟨67,66,68,68,.east,2,2,false,false⟩ : PushEdge) = true := by decide
theorem fact70 : pushFacts (⟨67,47,87,87,.south,2,2,false,false⟩ : PushEdge) = true := by decide
theorem fact71 : pushFacts (⟨67,68,66,66,.west,0,2,false,false⟩ : PushEdge) = true := by decide
end NetHack.Sokoban21
