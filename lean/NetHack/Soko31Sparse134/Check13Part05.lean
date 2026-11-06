import NetHack.Soko31Sparse134.CheckRow
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko31Sparse134
def heroes13part05 : List Nat := [239, 240, 241, 242, 262, 263, 264, 265, 267, 268, 269, 270]
theorem checked13part05 : heroes13part05.all (classifyRow 13) = true := by decide +kernel
end NetHack.Soko31Sparse134
