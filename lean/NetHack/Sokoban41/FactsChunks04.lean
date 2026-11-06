/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.FactsChunks03
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban41
theorem fact100 : pushFacts (⟨53,67,39,39,.north,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact101 : pushFacts (⟨53,39,67,67,.south,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact102 : pushFacts (⟨66,80,52,52,.north,2,10,false,false⟩ : PushEdge) = true := by decide
theorem fact103 : pushFacts (⟨66,52,80,80,.south,0,10,false,false⟩ : PushEdge) = true := by decide
theorem fact104 : pushFacts (⟨80,94,66,66,.north,2,11,false,false⟩ : PushEdge) = true := by decide
theorem fact105 : pushFacts (⟨80,66,94,94,.south,0,11,false,false⟩ : PushEdge) = true := by decide
theorem fact106 : pushFacts (⟨86,85,87,87,.east,0,20,false,false⟩ : PushEdge) = true := by decide
theorem fact107 : pushFacts (⟨86,87,85,85,.west,20,20,false,true⟩ : PushEdge) = true := by decide
theorem fact108 : pushFacts (⟨87,86,88,88,.east,0,0,false,false⟩ : PushEdge) = true := by decide
theorem fact109 : pushFacts (⟨87,88,86,86,.west,2,2,false,false⟩ : PushEdge) = true := by decide
theorem fact110 : pushFacts (⟨88,87,89,89,.east,2,22,false,false⟩ : PushEdge) = true := by decide
theorem fact111 : pushFacts (⟨88,89,87,87,.west,2,22,false,false⟩ : PushEdge) = true := by decide
theorem fact112 : pushFacts (⟨89,88,90,90,.east,21,21,false,true⟩ : PushEdge) = true := by decide
theorem fact113 : pushFacts (⟨89,90,88,88,.west,0,0,false,false⟩ : PushEdge) = true := by decide
theorem fact114 : pushFacts (⟨151,150,152,152,.east,15,15,false,true⟩ : PushEdge) = true := by decide
theorem fact115 : pushFacts (⟨151,152,150,150,.west,0,15,false,false⟩ : PushEdge) = true := by decide
theorem fact116 : pushFacts (⟨93,92,94,94,.east,0,11,false,false⟩ : PushEdge) = true := by decide
theorem fact117 : pushFacts (⟨93,94,92,92,.west,11,11,false,true⟩ : PushEdge) = true := by decide
theorem fact118 : pushFacts (⟨94,108,80,80,.north,2,12,false,false⟩ : PushEdge) = true := by decide
theorem fact119 : pushFacts (⟨94,93,95,95,.east,2,12,false,false⟩ : PushEdge) = true := by decide
theorem fact120 : pushFacts (⟨94,80,108,108,.south,0,12,false,false⟩ : PushEdge) = true := by decide
theorem fact121 : pushFacts (⟨94,95,93,93,.west,2,12,false,false⟩ : PushEdge) = true := by decide
theorem fact122 : pushFacts (⟨95,94,96,96,.east,11,11,false,true⟩ : PushEdge) = true := by decide
theorem fact123 : pushFacts (⟨95,96,94,94,.west,0,11,false,false⟩ : PushEdge) = true := by decide
theorem fact124 : pushFacts (⟨100,114,86,86,.north,1,1,false,false⟩ : PushEdge) = true := by decide
end NetHack.Sokoban41
