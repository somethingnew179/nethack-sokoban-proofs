import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0105_0_checked : (List.range' 53760 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0105_1_checked : (List.range' 53888 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0105_2_checked : (List.range' 54016 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0105_3_checked : (List.range' 54144 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0105_range (index : Nat) (lower : 53760 ≤ index) (upper : index < 54272) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 54016 then
    if cut : index < 53888 then
      exact segment_sound _ 53760 128 Numeric0105_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 53888 128 Numeric0105_1_checked index (by omega) (by omega)
  else
    if cut : index < 54144 then
      exact segment_sound _ 54016 128 Numeric0105_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 54144 128 Numeric0105_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
