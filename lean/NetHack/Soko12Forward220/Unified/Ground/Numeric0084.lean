import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0084_0_checked : (List.range' 43008 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0084_1_checked : (List.range' 43136 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0084_2_checked : (List.range' 43264 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0084_3_checked : (List.range' 43392 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0084_range (index : Nat) (lower : 43008 ≤ index) (upper : index < 43520) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 43264 then
    if cut : index < 43136 then
      exact segment_sound _ 43008 128 Numeric0084_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 43136 128 Numeric0084_1_checked index (by omega) (by omega)
  else
    if cut : index < 43392 then
      exact segment_sound _ 43264 128 Numeric0084_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 43392 128 Numeric0084_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
