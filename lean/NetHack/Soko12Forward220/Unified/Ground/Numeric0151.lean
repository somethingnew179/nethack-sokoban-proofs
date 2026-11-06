import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0151_0_checked : (List.range' 77312 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0151_1_checked : (List.range' 77440 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0151_2_checked : (List.range' 77568 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0151_3_checked : (List.range' 77696 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0151_range (index : Nat) (lower : 77312 ≤ index) (upper : index < 77824) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 77568 then
    if cut : index < 77440 then
      exact segment_sound _ 77312 128 Numeric0151_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 77440 128 Numeric0151_1_checked index (by omega) (by omega)
  else
    if cut : index < 77696 then
      exact segment_sound _ 77568 128 Numeric0151_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 77696 128 Numeric0151_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
