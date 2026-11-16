import Owner1007.RightCapacity12Data
namespace Owner1007.RightCapacity12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem upperNode1 : upperNode ⟨1,by decide⟩ = true := by decide +kernel
#print axioms upperNode1
end Owner1007.RightCapacity12
