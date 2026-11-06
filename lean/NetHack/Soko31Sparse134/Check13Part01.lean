import NetHack.Soko31Sparse134.CheckRow
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko31Sparse134
def heroes13part01 : List Nat := [64, 65, 66, 67, 68, 69, 88, 89, 90, 91, 92, 93]
theorem checked13part01 : heroes13part01.all (classifyRow 13) = true := by decide +kernel
end NetHack.Soko31Sparse134
