import NetHack.Soko31Sparse134.CheckRow
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko31Sparse134
def heroes14part00 : List Nat := [30, 31, 32, 33, 35, 36, 37, 38, 59, 60, 61, 62]
theorem checked14part00 : heroes14part00.all (classifyRow 14) = true := by decide +kernel
end NetHack.Soko31Sparse134
