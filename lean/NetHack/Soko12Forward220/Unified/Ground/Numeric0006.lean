import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0006_0_checked : (List.range' 3072 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0006_1_checked : (List.range' 3200 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0006_2_checked : (List.range' 3328 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0006_3_checked : (List.range' 3456 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0006_range (index : Nat) (lower : 3072 ≤ index) (upper : index < 3584) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 3328 then
    if cut : index < 3200 then
      exact segment_sound _ 3072 128 Numeric0006_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 3200 128 Numeric0006_1_checked index (by omega) (by omega)
  else
    if cut : index < 3456 then
      exact segment_sound _ 3328 128 Numeric0006_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 3456 128 Numeric0006_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
