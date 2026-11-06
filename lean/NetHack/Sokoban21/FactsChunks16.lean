/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.FactsChunks15
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
theorem fact128 : pushFacts (⟨107,87,127,127,.south,1,1,false,true⟩ : PushEdge) = true := by decide
theorem fact129 : pushFacts (⟨107,108,106,106,.west,1,1,false,true⟩ : PushEdge) = true := by decide
theorem fact130 : pushFacts (⟨108,107,109,109,.east,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact131 : pushFacts (⟨108,109,107,107,.west,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact132 : pushFacts (⟨109,108,110,110,.east,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact133 : pushFacts (⟨109,110,108,108,.west,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact134 : pushFacts (⟨110,130,90,90,.north,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact135 : pushFacts (⟨110,109,111,111,.east,1,1,false,false⟩ : PushEdge) = true := by decide
end NetHack.Sokoban21
