/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.FactsChunks16
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
theorem fact136 : pushFacts (⟨110,90,130,130,.south,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact137 : pushFacts (⟨110,111,109,109,.west,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact138 : pushFacts (⟨111,110,112,112,.east,1,1,false,true⟩ : PushEdge) = true := by decide
theorem fact139 : pushFacts (⟨111,112,110,110,.west,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact140 : pushFacts (⟨114,134,94,94,.north,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact141 : pushFacts (⟨114,94,134,134,.south,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact142 : pushFacts (⟨115,135,95,95,.north,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact143 : pushFacts (⟨115,114,116,116,.east,1,1,true,true⟩ : PushEdge) = true := by decide
end NetHack.Sokoban21
