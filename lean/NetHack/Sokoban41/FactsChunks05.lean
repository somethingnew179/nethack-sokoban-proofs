/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.FactsChunks04
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban41
theorem fact125 : pushFacts (⟨100,86,114,114,.south,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact126 : pushFacts (⟨106,120,92,92,.north,15,15,false,true⟩ : PushEdge) = true := by decide
theorem fact127 : pushFacts (⟨106,92,120,120,.south,0,15,false,false⟩ : PushEdge) = true := by decide
theorem fact128 : pushFacts (⟨107,121,93,93,.north,4,14,false,false⟩ : PushEdge) = true := by decide
theorem fact129 : pushFacts (⟨107,106,108,108,.east,2,14,false,false⟩ : PushEdge) = true := by decide
theorem fact130 : pushFacts (⟨107,93,121,121,.south,0,14,false,false⟩ : PushEdge) = true := by decide
theorem fact131 : pushFacts (⟨107,108,106,106,.west,0,14,false,false⟩ : PushEdge) = true := by decide
theorem fact132 : pushFacts (⟨108,122,94,94,.north,2,13,false,false⟩ : PushEdge) = true := by decide
theorem fact133 : pushFacts (⟨108,107,109,109,.east,2,13,false,false⟩ : PushEdge) = true := by decide
theorem fact134 : pushFacts (⟨108,94,122,122,.south,0,13,false,false⟩ : PushEdge) = true := by decide
theorem fact135 : pushFacts (⟨108,109,107,107,.west,0,13,false,false⟩ : PushEdge) = true := by decide
theorem fact136 : pushFacts (⟨109,123,95,95,.north,2,12,false,false⟩ : PushEdge) = true := by decide
theorem fact137 : pushFacts (⟨109,108,110,110,.east,12,12,false,true⟩ : PushEdge) = true := by decide
theorem fact138 : pushFacts (⟨109,95,123,123,.south,0,12,false,false⟩ : PushEdge) = true := by decide
theorem fact139 : pushFacts (⟨109,110,108,108,.west,0,12,false,false⟩ : PushEdge) = true := by decide
theorem fact140 : pushFacts (⟨110,124,96,96,.north,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact141 : pushFacts (⟨110,96,124,124,.south,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact142 : pushFacts (⟨114,128,100,100,.north,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact143 : pushFacts (⟨114,100,128,114,.south,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact144 : pushFacts (⟨114,100,128,128,.south,2,20,false,false⟩ : PushEdge) = true := by decide
theorem fact145 : pushFacts (⟨114,100,128,142,.south,2,2,false,false⟩ : PushEdge) = true := by decide
theorem fact146 : pushFacts (⟨114,100,128,156,.south,20,20,false,true⟩ : PushEdge) = true := by decide
theorem fact147 : pushFacts (⟨150,149,151,151,.east,2,16,false,false⟩ : PushEdge) = true := by decide
theorem fact148 : pushFacts (⟨150,151,149,149,.west,0,16,false,false⟩ : PushEdge) = true := by decide
theorem fact149 : pushFacts (⟨120,134,106,106,.north,2,16,false,false⟩ : PushEdge) = true := by decide
end NetHack.Sokoban41
