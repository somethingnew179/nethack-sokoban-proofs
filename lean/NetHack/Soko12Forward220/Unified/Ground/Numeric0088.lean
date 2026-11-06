import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0088_0_checked : (List.range' 45056 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0088_1_checked : (List.range' 45184 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0088_2_checked : (List.range' 45312 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0088_3_checked : (List.range' 45440 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0088_range (index : Nat) (lower : 45056 ≤ index) (upper : index < 45568) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 45312 then
    if cut : index < 45184 then
      exact segment_sound _ 45056 128 Numeric0088_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 45184 128 Numeric0088_1_checked index (by omega) (by omega)
  else
    if cut : index < 45440 then
      exact segment_sound _ 45312 128 Numeric0088_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 45440 128 Numeric0088_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
