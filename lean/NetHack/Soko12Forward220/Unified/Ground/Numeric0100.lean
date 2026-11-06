import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0100_0_checked : (List.range' 51200 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0100_1_checked : (List.range' 51328 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0100_2_checked : (List.range' 51456 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0100_3_checked : (List.range' 51584 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0100_range (index : Nat) (lower : 51200 ≤ index) (upper : index < 51712) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 51456 then
    if cut : index < 51328 then
      exact segment_sound _ 51200 128 Numeric0100_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 51328 128 Numeric0100_1_checked index (by omega) (by omega)
  else
    if cut : index < 51584 then
      exact segment_sound _ 51456 128 Numeric0100_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 51584 128 Numeric0100_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
