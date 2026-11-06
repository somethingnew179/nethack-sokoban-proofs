import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0116_0_checked : (List.range' 59392 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0116_1_checked : (List.range' 59520 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0116_2_checked : (List.range' 59648 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0116_3_checked : (List.range' 59776 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0116_range (index : Nat) (lower : 59392 ≤ index) (upper : index < 59904) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 59648 then
    if cut : index < 59520 then
      exact segment_sound _ 59392 128 Numeric0116_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 59520 128 Numeric0116_1_checked index (by omega) (by omega)
  else
    if cut : index < 59776 then
      exact segment_sound _ 59648 128 Numeric0116_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 59776 128 Numeric0116_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
