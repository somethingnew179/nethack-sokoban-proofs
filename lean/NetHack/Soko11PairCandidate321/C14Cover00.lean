import NetHack.Soko11PairCandidate321.Coverage14Data
namespace NetHack.Soko11PairCandidate321
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked14slice00 : ((NetHack.Soko11Hero315.phases.crates 14).drop 0 |>.take 16).all coverageRow14 = true := by decide +kernel
end NetHack.Soko11PairCandidate321
