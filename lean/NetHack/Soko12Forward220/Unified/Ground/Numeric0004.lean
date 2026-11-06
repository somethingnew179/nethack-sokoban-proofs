import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0004_0_checked : (List.range' 2048 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0004_1_checked : (List.range' 2176 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0004_2_checked : (List.range' 2304 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0004_3_checked : (List.range' 2432 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0004_range (index : Nat) (lower : 2048 ≤ index) (upper : index < 2560) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 2304 then
    if cut : index < 2176 then
      exact segment_sound _ 2048 128 Numeric0004_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 2176 128 Numeric0004_1_checked index (by omega) (by omega)
  else
    if cut : index < 2432 then
      exact segment_sound _ 2304 128 Numeric0004_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 2432 128 Numeric0004_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
