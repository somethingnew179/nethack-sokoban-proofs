/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.Rows
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban41
theorem fact0 : pushFacts (⟨128,142,114,114,.north,0,0,false,false⟩ : PushEdge) = true := by decide
theorem fact1 : pushFacts (⟨128,114,142,142,.south,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact2 : pushFacts (⟨134,148,120,120,.north,2,17,false,false⟩ : PushEdge) = true := by decide
theorem fact3 : pushFacts (⟨134,120,148,148,.south,0,17,false,false⟩ : PushEdge) = true := by decide
theorem fact4 : pushFacts (⟨135,149,121,121,.north,2,16,false,false⟩ : PushEdge) = true := by decide
theorem fact5 : pushFacts (⟨135,134,136,136,.east,2,16,false,false⟩ : PushEdge) = true := by decide
theorem fact6 : pushFacts (⟨135,121,149,149,.south,0,16,false,false⟩ : PushEdge) = true := by decide
theorem fact7 : pushFacts (⟨135,136,134,134,.west,0,16,false,false⟩ : PushEdge) = true := by decide
theorem fact8 : pushFacts (⟨136,150,122,122,.north,2,15,false,false⟩ : PushEdge) = true := by decide
theorem fact9 : pushFacts (⟨136,135,137,137,.east,2,15,false,false⟩ : PushEdge) = true := by decide
theorem fact10 : pushFacts (⟨136,122,150,150,.south,0,15,false,false⟩ : PushEdge) = true := by decide
theorem fact11 : pushFacts (⟨136,137,135,135,.west,0,15,false,false⟩ : PushEdge) = true := by decide
theorem fact12 : pushFacts (⟨137,151,123,123,.north,2,14,false,false⟩ : PushEdge) = true := by decide
theorem fact13 : pushFacts (⟨137,136,138,138,.east,14,14,false,true⟩ : PushEdge) = true := by decide
theorem fact14 : pushFacts (⟨137,123,151,151,.south,0,14,false,false⟩ : PushEdge) = true := by decide
theorem fact15 : pushFacts (⟨137,138,136,136,.west,0,14,false,false⟩ : PushEdge) = true := by decide
theorem fact16 : pushFacts (⟨138,152,124,124,.north,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact17 : pushFacts (⟨138,124,152,152,.south,1,1,true,true⟩ : PushEdge) = true := by decide
theorem fact18 : pushFacts (⟨142,156,128,142,.north,1,1,false,false⟩ : PushEdge) = true := by decide
theorem fact19 : pushFacts (⟨142,156,128,128,.north,1,19,false,false⟩ : PushEdge) = true := by decide
theorem fact20 : pushFacts (⟨142,156,128,114,.north,0,0,false,false⟩ : PushEdge) = true := by decide
theorem fact21 : pushFacts (⟨142,156,128,100,.north,0,0,false,false⟩ : PushEdge) = true := by decide
theorem fact22 : pushFacts (⟨142,156,128,86,.north,0,0,false,false⟩ : PushEdge) = true := by decide
theorem fact23 : pushFacts (⟨142,128,156,156,.south,19,19,false,true⟩ : PushEdge) = true := by decide
theorem fact24 : pushFacts (⟨16,15,17,17,.east,1,1,true,true⟩ : PushEdge) = true := by decide
end NetHack.Sokoban41
