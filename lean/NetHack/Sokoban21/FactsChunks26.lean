/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.FactsChunks25
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
theorem fact208 : pushFacts (⟨162,182,142,142,.north,2,14,false,false⟩ : PushEdge) = true := by decide
theorem fact209 : pushFacts (⟨162,142,182,182,.south,0,14,false,false⟩ : PushEdge) = true := by decide
theorem fact210 : pushFacts (⟨163,183,143,143,.north,2,15,false,false⟩ : PushEdge) = true := by decide
theorem fact211 : pushFacts (⟨163,143,183,183,.south,0,15,false,false⟩ : PushEdge) = true := by decide
theorem fact212 : pushFacts (⟨165,185,145,145,.north,2,17,false,false⟩ : PushEdge) = true := by decide
theorem fact213 : pushFacts (⟨165,145,185,185,.south,0,17,false,false⟩ : PushEdge) = true := by decide
theorem fact214 : pushFacts (⟨166,186,146,146,.north,2,18,false,false⟩ : PushEdge) = true := by decide
theorem fact215 : pushFacts (⟨166,146,186,186,.south,0,18,false,false⟩ : PushEdge) = true := by decide
end NetHack.Sokoban21
