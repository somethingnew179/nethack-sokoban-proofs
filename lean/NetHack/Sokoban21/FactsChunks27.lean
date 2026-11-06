/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.FactsChunks26
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
theorem fact216 : pushFacts (⟨182,202,162,162,.north,2,15,false,false⟩ : PushEdge) = true := by decide
theorem fact217 : pushFacts (⟨182,181,183,183,.east,0,15,false,false⟩ : PushEdge) = true := by decide
theorem fact218 : pushFacts (⟨182,162,202,202,.south,15,15,false,true⟩ : PushEdge) = true := by decide
theorem fact219 : pushFacts (⟨182,183,181,181,.west,15,15,false,true⟩ : PushEdge) = true := by decide
theorem fact220 : pushFacts (⟨183,203,163,163,.north,2,16,false,false⟩ : PushEdge) = true := by decide
theorem fact221 : pushFacts (⟨183,182,184,184,.east,0,16,false,false⟩ : PushEdge) = true := by decide
theorem fact222 : pushFacts (⟨183,163,203,203,.south,16,16,false,true⟩ : PushEdge) = true := by decide
theorem fact223 : pushFacts (⟨183,184,182,182,.west,2,16,false,false⟩ : PushEdge) = true := by decide
end NetHack.Sokoban21
