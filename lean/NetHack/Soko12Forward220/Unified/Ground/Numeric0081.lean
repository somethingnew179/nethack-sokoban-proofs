import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0081_0_checked : (List.range' 41472 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0081_1_checked : (List.range' 41600 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0081_2_checked : (List.range' 41728 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0081_3_checked : (List.range' 41856 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0081_range (index : Nat) (lower : 41472 ≤ index) (upper : index < 41984) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 41728 then
    if cut : index < 41600 then
      exact segment_sound _ 41472 128 Numeric0081_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 41600 128 Numeric0081_1_checked index (by omega) (by omega)
  else
    if cut : index < 41856 then
      exact segment_sound _ 41728 128 Numeric0081_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 41856 128 Numeric0081_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
