/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.FactsChunks14
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
theorem fact120 : pushFacts (⟨98,118,78,78,.north,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact121 : pushFacts (⟨98,78,118,118,.south,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact122 : pushFacts (⟨102,122,82,82,.north,2,11,false,false⟩ : PushEdge) = true := by decide
theorem fact123 : pushFacts (⟨102,101,103,103,.east,11,11,false,true⟩ : PushEdge) = true := by decide
theorem fact124 : pushFacts (⟨102,82,122,122,.south,0,11,false,false⟩ : PushEdge) = true := by decide
theorem fact125 : pushFacts (⟨102,103,101,101,.west,11,11,false,true⟩ : PushEdge) = true := by decide
theorem fact126 : pushFacts (⟨107,127,87,87,.north,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact127 : pushFacts (⟨107,106,108,108,.east,1,1,false,false⟩ : PushEdge) = true := by decide
end NetHack.Sokoban21
