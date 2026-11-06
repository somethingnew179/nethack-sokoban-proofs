import NetHack.Sokoban.PatternBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.PatternCertificate

/- Only K-source moves can decrease the monotone occupancy bonus. The other
rows are discharged analytically in local_bounds, not silently omitted. -/
def activeEdges : List Edge := [
  ⟨20,35,50,50,.south,1,1⟩,
  ⟨21,36,51,51,.south,1,1⟩,
  ⟨34,35,36,36,.east,1,1⟩,
  ⟨35,36,37,37,.east,0,1⟩,
  ⟨36,37,38,38,.east,0,2⟩,
  ⟨36,51,66,66,.south,1,1⟩,
  ⟨36,35,34,34,.west,1,1⟩,
  ⟨37,52,67,67,.south,1,1⟩,
  ⟨37,36,35,35,.west,1,1⟩,
  ⟨38,37,36,36,.west,2,2⟩,
  ⟨50,35,20,20,.north,1,1⟩,
  ⟨50,51,52,52,.east,1,1⟩,
  ⟨51,36,21,21,.north,1,1⟩,
  ⟨52,51,50,50,.west,1,1⟩,
  ⟨66,51,36,36,.north,1,1⟩,
  ⟨67,52,37,37,.north,0,1⟩,
  ⟨113,128,143,143,.south,13,13⟩,
  ⟨114,129,144,144,.south,12,12⟩,
  ⟨115,130,145,145,.south,11,11⟩,
  ⟨126,127,128,128,.east,2,14⟩,
  ⟨127,128,129,129,.east,2,13⟩,
  ⟨128,129,130,130,.east,2,12⟩,
  ⟨128,127,126,127,.west,1,14⟩,
  ⟨128,127,126,126,.west,1,14⟩,
  ⟨128,127,126,125,.west,0,0⟩,
  ⟨128,127,126,124,.west,0,0⟩,
  ⟨128,127,126,123,.west,0,0⟩,
  ⟨128,127,126,122,.west,0,0⟩,
  ⟨128,127,126,121,.west,0,0⟩,
  ⟨129,130,131,131,.east,2,11⟩,
  ⟨129,128,127,127,.west,0,13⟩,
  ⟨130,129,128,128,.west,0,12⟩,
  ⟨131,130,129,129,.west,0,11⟩,
  ⟨143,128,113,113,.north,2,13⟩,
  ⟨144,129,114,114,.north,2,12⟩,
  ⟨145,130,115,115,.north,2,11⟩]

theorem active_exact : activeEdges = edges.filter (fun edge => support.contains edge.source) := by decide

theorem all_patterns_checked : allPatterns.all (fun pattern => activeEdges.all (rowCheck pattern)) = true := by decide

end NetHack.Sokoban.PatternCertificate
