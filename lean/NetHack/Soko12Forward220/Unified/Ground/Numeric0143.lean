import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0143_0_checked : (List.range' 73216 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0143_1_checked : (List.range' 73344 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0143_2_checked : (List.range' 73472 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0143_3_checked : (List.range' 73600 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0143_range (index : Nat) (lower : 73216 ≤ index) (upper : index < 73728) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 73472 then
    if cut : index < 73344 then
      exact segment_sound _ 73216 128 Numeric0143_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 73344 128 Numeric0143_1_checked index (by omega) (by omega)
  else
    if cut : index < 73600 then
      exact segment_sound _ 73472 128 Numeric0143_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 73600 128 Numeric0143_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
