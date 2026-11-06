import NetHack.Soko31Sparse134.CheckRow
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko31Sparse134
def heroes14part04 : List Nat := [207, 209, 210, 211, 212, 213, 233, 234, 235, 236, 237, 238]
theorem checked14part04 : heroes14part04.all (classifyRow 14) = true := by decide +kernel
end NetHack.Soko31Sparse134
