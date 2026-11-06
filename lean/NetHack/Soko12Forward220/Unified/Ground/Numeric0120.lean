import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0120_0_checked : (List.range' 61440 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0120_1_checked : (List.range' 61568 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0120_2_checked : (List.range' 61696 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0120_3_checked : (List.range' 61824 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0120_range (index : Nat) (lower : 61440 ≤ index) (upper : index < 61952) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 61696 then
    if cut : index < 61568 then
      exact segment_sound _ 61440 128 Numeric0120_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 61568 128 Numeric0120_1_checked index (by omega) (by omega)
  else
    if cut : index < 61824 then
      exact segment_sound _ 61696 128 Numeric0120_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 61824 128 Numeric0120_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
