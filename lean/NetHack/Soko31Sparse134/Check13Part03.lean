import NetHack.Soko31Sparse134.CheckRow
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko31Sparse134
def heroes13part03 : List Nat := [175, 176, 177, 178, 180, 181, 182, 183, 184, 204, 205, 206]
theorem checked13part03 : heroes13part03.all (classifyRow 13) = true := by decide +kernel
end NetHack.Soko31Sparse134
