import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0056_0_checked : (List.range' 28672 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0056_1_checked : (List.range' 28800 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0056_2_checked : (List.range' 28928 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0056_3_checked : (List.range' 29056 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0056_range (index : Nat) (lower : 28672 ≤ index) (upper : index < 29184) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 28928 then
    if cut : index < 28800 then
      exact segment_sound _ 28672 128 Numeric0056_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 28800 128 Numeric0056_1_checked index (by omega) (by omega)
  else
    if cut : index < 29056 then
      exact segment_sound _ 28928 128 Numeric0056_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 29056 128 Numeric0056_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
