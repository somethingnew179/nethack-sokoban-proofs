import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0117_0_checked : (List.range' 59904 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0117_1_checked : (List.range' 60032 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0117_2_checked : (List.range' 60160 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0117_3_checked : (List.range' 60288 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0117_range (index : Nat) (lower : 59904 ≤ index) (upper : index < 60416) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 60160 then
    if cut : index < 60032 then
      exact segment_sound _ 59904 128 Numeric0117_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 60032 128 Numeric0117_1_checked index (by omega) (by omega)
  else
    if cut : index < 60288 then
      exact segment_sound _ 60160 128 Numeric0117_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 60288 128 Numeric0117_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
