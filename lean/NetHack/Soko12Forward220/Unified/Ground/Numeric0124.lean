import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0124_0_checked : (List.range' 63488 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0124_1_checked : (List.range' 63616 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0124_2_checked : (List.range' 63744 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0124_3_checked : (List.range' 63872 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0124_range (index : Nat) (lower : 63488 ≤ index) (upper : index < 64000) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 63744 then
    if cut : index < 63616 then
      exact segment_sound _ 63488 128 Numeric0124_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 63616 128 Numeric0124_1_checked index (by omega) (by omega)
  else
    if cut : index < 63872 then
      exact segment_sound _ 63744 128 Numeric0124_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 63872 128 Numeric0124_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
