import Owner1007.NorthEvents12Data
namespace Owner1007.NorthEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem node2 : nodeCheck ⟨2,by decide⟩ = true := by decide +kernel
theorem guard2 : GuardNode ⟨2,by decide⟩ := by
  unfold GuardNode
  decide +kernel
#print axioms node2
#print axioms guard2
end Owner1007.NorthEvents12
