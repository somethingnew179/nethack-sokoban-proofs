/- Two full initial-pair rows only. Changed pair positions remain unchecked. -/
import NetHack.Soko11PairCandidate321.CheckRow
namespace NetHack.Soko11PairCandidate321
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem pilot139191 : rowCheck 0 [139,191] = true := by decide +kernel
theorem pilot186212 : rowCheck 0 [186,212] = true := by decide +kernel
end NetHack.Soko11PairCandidate321
