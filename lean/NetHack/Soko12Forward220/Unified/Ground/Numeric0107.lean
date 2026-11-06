import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0107_0_checked : (List.range' 54784 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0107_1_checked : (List.range' 54912 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0107_2_checked : (List.range' 55040 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0107_3_checked : (List.range' 55168 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0107_range (index : Nat) (lower : 54784 ≤ index) (upper : index < 55296) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 55040 then
    if cut : index < 54912 then
      exact segment_sound _ 54784 128 Numeric0107_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 54912 128 Numeric0107_1_checked index (by omega) (by omega)
  else
    if cut : index < 55168 then
      exact segment_sound _ 55040 128 Numeric0107_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 55168 128 Numeric0107_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
