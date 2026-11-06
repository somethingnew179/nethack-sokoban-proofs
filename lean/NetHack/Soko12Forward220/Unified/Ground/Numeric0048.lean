import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0048_0_checked : (List.range' 24576 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0048_1_checked : (List.range' 24704 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0048_2_checked : (List.range' 24832 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0048_3_checked : (List.range' 24960 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0048_range (index : Nat) (lower : 24576 ≤ index) (upper : index < 25088) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 24832 then
    if cut : index < 24704 then
      exact segment_sound _ 24576 128 Numeric0048_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 24704 128 Numeric0048_1_checked index (by omega) (by omega)
  else
    if cut : index < 24960 then
      exact segment_sound _ 24832 128 Numeric0048_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 24960 128 Numeric0048_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
