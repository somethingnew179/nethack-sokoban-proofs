import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0055_0_checked : (List.range' 28160 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0055_1_checked : (List.range' 28288 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0055_2_checked : (List.range' 28416 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0055_3_checked : (List.range' 28544 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0055_range (index : Nat) (lower : 28160 ≤ index) (upper : index < 28672) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 28416 then
    if cut : index < 28288 then
      exact segment_sound _ 28160 128 Numeric0055_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 28288 128 Numeric0055_1_checked index (by omega) (by omega)
  else
    if cut : index < 28544 then
      exact segment_sound _ 28416 128 Numeric0055_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 28544 128 Numeric0055_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
