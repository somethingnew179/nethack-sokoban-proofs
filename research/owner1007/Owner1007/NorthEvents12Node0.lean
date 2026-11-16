import Owner1007.NorthEvents12Data
namespace Owner1007.NorthEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem node0 : nodeCheck ⟨0,by decide⟩ = true := by decide +kernel
theorem guard0 : GuardNode ⟨0,by decide⟩ := by
  unfold GuardNode
  decide +kernel
#print axioms node0
#print axioms guard0
end Owner1007.NorthEvents12
