import Owner1007.PairPath11Data
namespace Owner1007.PairPath11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem node6 : nodeCheck ⟨6,by decide⟩ = true := by decide +kernel
theorem node7 : nodeCheck ⟨7,by decide⟩ = true := by decide +kernel
theorem node8 : nodeCheck ⟨8,by decide⟩ = true := by decide +kernel
#print axioms node8
end Owner1007.PairPath11
