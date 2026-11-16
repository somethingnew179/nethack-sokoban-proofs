import Owner1007.PairPath11Data
namespace Owner1007.PairPath11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem node3 : nodeCheck ⟨3,by decide⟩ = true := by decide +kernel
theorem node4 : nodeCheck ⟨4,by decide⟩ = true := by decide +kernel
theorem node5 : nodeCheck ⟨5,by decide⟩ = true := by decide +kernel
#print axioms node5
end Owner1007.PairPath11
