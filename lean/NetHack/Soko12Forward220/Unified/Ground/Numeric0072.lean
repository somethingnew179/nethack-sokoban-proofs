import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0072_0_checked : (List.range' 36864 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0072_1_checked : (List.range' 36992 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0072_2_checked : (List.range' 37120 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0072_3_checked : (List.range' 37248 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0072_range (index : Nat) (lower : 36864 ≤ index) (upper : index < 37376) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 37120 then
    if cut : index < 36992 then
      exact segment_sound _ 36864 128 Numeric0072_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 36992 128 Numeric0072_1_checked index (by omega) (by omega)
  else
    if cut : index < 37248 then
      exact segment_sound _ 37120 128 Numeric0072_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 37248 128 Numeric0072_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
