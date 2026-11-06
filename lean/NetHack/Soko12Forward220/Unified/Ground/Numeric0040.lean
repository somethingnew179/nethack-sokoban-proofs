import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0040_0_checked : (List.range' 20480 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0040_1_checked : (List.range' 20608 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0040_2_checked : (List.range' 20736 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0040_3_checked : (List.range' 20864 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0040_range (index : Nat) (lower : 20480 ≤ index) (upper : index < 20992) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 20736 then
    if cut : index < 20608 then
      exact segment_sound _ 20480 128 Numeric0040_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 20608 128 Numeric0040_1_checked index (by omega) (by omega)
  else
    if cut : index < 20864 then
      exact segment_sound _ 20736 128 Numeric0040_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 20864 128 Numeric0040_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
