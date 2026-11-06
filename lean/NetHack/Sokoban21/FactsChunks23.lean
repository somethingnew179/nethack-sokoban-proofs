/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.FactsChunks22
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
theorem fact184 : pushFacts (⟨137,157,117,117,.north,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact185 : pushFacts (⟨137,136,138,138,.east,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact186 : pushFacts (⟨137,117,157,157,.south,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact187 : pushFacts (⟨137,138,136,136,.west,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact188 : pushFacts (⟨138,158,118,118,.north,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact189 : pushFacts (⟨138,118,158,158,.south,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact190 : pushFacts (⟨142,162,122,122,.north,2,13,false,false⟩ : PushEdge) = true := by decide
theorem fact191 : pushFacts (⟨142,141,143,143,.east,0,13,false,false⟩ : PushEdge) = true := by decide
end NetHack.Sokoban21
