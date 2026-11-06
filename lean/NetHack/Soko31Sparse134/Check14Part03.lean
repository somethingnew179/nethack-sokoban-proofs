import NetHack.Soko31Sparse134.CheckRow
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko31Sparse134
def heroes14part03 : List Nat := [175, 176, 177, 178, 180, 181, 182, 183, 184, 204, 205, 206]
theorem checked14part03 : heroes14part03.all (classifyRow 14) = true := by decide +kernel
end NetHack.Soko31Sparse134
