/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.FactsChunks05
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
theorem fact48 : pushFacts (⟨56,76,36,36,.north,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact49 : pushFacts (⟨56,55,57,57,.east,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact50 : pushFacts (⟨56,36,76,76,.south,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact51 : pushFacts (⟨56,57,55,55,.west,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact52 : pushFacts (⟨57,77,37,37,.north,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact53 : pushFacts (⟨57,56,58,58,.east,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact54 : pushFacts (⟨57,37,77,77,.south,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact55 : pushFacts (⟨57,58,56,56,.west,1,1,true,true⟩ : PushEdge) = true := by decide
end NetHack.Sokoban21
