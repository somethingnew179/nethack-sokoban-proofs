import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0038_0_checked : (List.range' 19456 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0038_1_checked : (List.range' 19584 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0038_2_checked : (List.range' 19712 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0038_3_checked : (List.range' 19840 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0038_range (index : Nat) (lower : 19456 ≤ index) (upper : index < 19968) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 19712 then
    if cut : index < 19584 then
      exact segment_sound _ 19456 128 Numeric0038_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 19584 128 Numeric0038_1_checked index (by omega) (by omega)
  else
    if cut : index < 19840 then
      exact segment_sound _ 19712 128 Numeric0038_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 19840 128 Numeric0038_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
