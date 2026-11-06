import NetHack.Soko31Sparse134.CheckRow
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko31Sparse134
def heroes13part02 : List Nat := [94, 95, 96, 117, 118, 119, 120, 122, 123, 124, 125, 147]
theorem checked13part02 : heroes13part02.all (classifyRow 13) = true := by decide +kernel
end NetHack.Soko31Sparse134
