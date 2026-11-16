import Owner1007.NorthEvents12Data
namespace Owner1007.NorthEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem node1 : nodeCheck ⟨1,by decide⟩ = true := by decide +kernel
theorem guard1 : GuardNode ⟨1,by decide⟩ := by
  unfold GuardNode
  decide +kernel
#print axioms node1
#print axioms guard1
end Owner1007.NorthEvents12
