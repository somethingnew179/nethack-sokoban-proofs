/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.FactsChunks00
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban41
theorem fact25 : pushFacts (⟨16,17,15,15,.west,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact26 : pushFacts (⟨17,16,18,18,.east,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact27 : pushFacts (⟨17,18,16,16,.west,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact28 : pushFacts (⟨143,142,144,144,.east,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact29 : pushFacts (⟨143,144,142,142,.west,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact30 : pushFacts (⟨144,143,145,145,.east,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact31 : pushFacts (⟨144,145,143,143,.west,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact32 : pushFacts (⟨145,144,146,146,.east,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact33 : pushFacts (⟨145,146,144,144,.west,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact34 : pushFacts (⟨146,145,147,146,.east,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact35 : pushFacts (⟨146,145,147,147,.east,2,19,false,false⟩ : PushEdge) = true := by decide
theorem fact36 : pushFacts (⟨146,145,147,148,.east,2,19,false,false⟩ : PushEdge) = true := by decide
theorem fact37 : pushFacts (⟨146,145,147,149,.east,3,19,false,false⟩ : PushEdge) = true := by decide
theorem fact38 : pushFacts (⟨146,145,147,150,.east,4,19,false,false⟩ : PushEdge) = true := by decide
theorem fact39 : pushFacts (⟨146,145,147,151,.east,5,19,false,false⟩ : PushEdge) = true := by decide
theorem fact40 : pushFacts (⟨146,145,147,152,.east,19,19,false,true⟩ : PushEdge) = true := by decide
theorem fact41 : pushFacts (⟨146,147,145,145,.west,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact42 : pushFacts (⟨24,23,25,25,.east,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact43 : pushFacts (⟨24,25,23,23,.west,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact44 : pushFacts (⟨147,146,148,148,.east,1,18,false,false⟩ : PushEdge) = true := by decide
theorem fact45 : pushFacts (⟨147,148,146,146,.west,0,0,false,false⟩ : PushEdge) = true := by decide
theorem fact46 : pushFacts (⟨148,147,149,149,.east,2,18,false,false⟩ : PushEdge) = true := by decide
theorem fact47 : pushFacts (⟨148,149,147,148,.west,1,18,false,false⟩ : PushEdge) = true := by decide
theorem fact48 : pushFacts (⟨148,149,147,147,.west,1,18,false,false⟩ : PushEdge) = true := by decide
theorem fact49 : pushFacts (⟨148,149,147,146,.west,0,0,false,false⟩ : PushEdge) = true := by decide
end NetHack.Sokoban41
