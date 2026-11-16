import Owner1007.NorthEvents12Data
namespace Owner1007.NorthEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem node3 : nodeCheck ⟨3,by decide⟩ = true := by decide +kernel
theorem guard3 : GuardNode ⟨3,by decide⟩ := by
  unfold GuardNode
  decide +kernel
#print axioms node3
#print axioms guard3
end Owner1007.NorthEvents12
