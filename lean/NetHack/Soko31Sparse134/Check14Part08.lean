import NetHack.Soko31Sparse134.CheckRow
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko31Sparse134
def heroes14part08 : List Nat := [315]
theorem checked14part08 : heroes14part08.all (classifyRow 14) = true := by decide +kernel
end NetHack.Soko31Sparse134
