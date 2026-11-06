/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.FactsChunks27
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
theorem fact224 : pushFacts (⟨184,183,185,185,.east,0,17,false,false⟩ : PushEdge) = true := by decide
theorem fact225 : pushFacts (⟨184,185,183,183,.west,2,17,false,false⟩ : PushEdge) = true := by decide
theorem fact226 : pushFacts (⟨185,205,165,165,.north,2,18,false,false⟩ : PushEdge) = true := by decide
theorem fact227 : pushFacts (⟨185,184,186,186,.east,0,18,false,false⟩ : PushEdge) = true := by decide
theorem fact228 : pushFacts (⟨185,165,205,205,.south,18,18,false,true⟩ : PushEdge) = true := by decide
theorem fact229 : pushFacts (⟨185,186,184,184,.west,2,18,false,false⟩ : PushEdge) = true := by decide
theorem fact230 : pushFacts (⟨186,206,166,166,.north,2,19,false,false⟩ : PushEdge) = true := by decide
theorem fact231 : pushFacts (⟨186,185,187,186,.east,1,19,false,false⟩ : PushEdge) = true := by decide
end NetHack.Sokoban21
