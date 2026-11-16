import Owner1007.NorthEvents12Data
namespace Owner1007.NorthEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem node4 : nodeCheck ⟨4,by decide⟩ = true := by decide +kernel
theorem guard4 : GuardNode ⟨4,by decide⟩ := by
  unfold GuardNode
  decide +kernel
#print axioms node4
#print axioms guard4
end Owner1007.NorthEvents12
