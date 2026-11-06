import NetHack.Soko31Sparse134.CheckRow
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko31Sparse134
def heroes14part02 : List Nat := [94, 95, 96, 117, 118, 119, 120, 122, 123, 124, 125, 147]
theorem checked14part02 : heroes14part02.all (classifyRow 14) = true := by decide +kernel
end NetHack.Soko31Sparse134
