import Owner1007.PairPath11Data
namespace Owner1007.PairPath11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem node0 : nodeCheck ⟨0,by decide⟩ = true := by decide +kernel
theorem node1 : nodeCheck ⟨1,by decide⟩ = true := by decide +kernel
theorem node2 : nodeCheck ⟨2,by decide⟩ = true := by decide +kernel
#print axioms node2
end Owner1007.PairPath11
