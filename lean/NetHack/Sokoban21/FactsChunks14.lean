/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.FactsChunks13
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
theorem fact112 : pushFacts (⟨96,116,76,76,.north,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact113 : pushFacts (⟨96,95,97,97,.east,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact114 : pushFacts (⟨96,76,116,116,.south,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact115 : pushFacts (⟨96,97,95,95,.west,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact116 : pushFacts (⟨97,117,77,77,.north,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact117 : pushFacts (⟨97,96,98,98,.east,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact118 : pushFacts (⟨97,77,117,117,.south,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact119 : pushFacts (⟨97,98,96,96,.west,1,1,true,true⟩ : PushEdge) = true := by decide
end NetHack.Sokoban21
