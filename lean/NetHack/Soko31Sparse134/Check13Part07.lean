import NetHack.Soko31Sparse134.CheckRow
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko31Sparse134
def heroes13part07 : List Nat := [303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314]
theorem checked13part07 : heroes13part07.all (classifyRow 13) = true := by decide +kernel
end NetHack.Soko31Sparse134
