import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0080_0_checked : (List.range' 40960 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0080_1_checked : (List.range' 41088 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0080_2_checked : (List.range' 41216 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0080_3_checked : (List.range' 41344 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0080_range (index : Nat) (lower : 40960 ≤ index) (upper : index < 41472) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 41216 then
    if cut : index < 41088 then
      exact segment_sound _ 40960 128 Numeric0080_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 41088 128 Numeric0080_1_checked index (by omega) (by omega)
  else
    if cut : index < 41344 then
      exact segment_sound _ 41216 128 Numeric0080_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 41344 128 Numeric0080_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
