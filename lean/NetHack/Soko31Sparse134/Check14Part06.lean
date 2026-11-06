import NetHack.Soko31Sparse134.CheckRow
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko31Sparse134
def heroes14part06 : List Nat := [271, 291, 292, 293, 294, 296, 297, 298, 299, 300, 301, 302]
theorem checked14part06 : heroes14part06.all (classifyRow 14) = true := by decide +kernel
end NetHack.Soko31Sparse134
