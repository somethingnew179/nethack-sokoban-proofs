/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.FactsChunks17
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
theorem fact144 : pushFacts (⟨115,95,135,135,.south,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact145 : pushFacts (⟨115,116,114,114,.west,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact146 : pushFacts (⟨116,136,96,96,.north,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact147 : pushFacts (⟨116,115,117,117,.east,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact148 : pushFacts (⟨116,96,136,136,.south,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact149 : pushFacts (⟨116,117,115,115,.west,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact150 : pushFacts (⟨117,137,97,97,.north,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact151 : pushFacts (⟨117,116,118,118,.east,1,1,true,true⟩ : PushEdge) = true := by decide
end NetHack.Sokoban21
