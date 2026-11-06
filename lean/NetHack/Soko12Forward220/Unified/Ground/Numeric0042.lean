import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0042_0_checked : (List.range' 21504 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0042_1_checked : (List.range' 21632 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0042_2_checked : (List.range' 21760 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0042_3_checked : (List.range' 21888 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0042_range (index : Nat) (lower : 21504 ≤ index) (upper : index < 22016) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 21760 then
    if cut : index < 21632 then
      exact segment_sound _ 21504 128 Numeric0042_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 21632 128 Numeric0042_1_checked index (by omega) (by omega)
  else
    if cut : index < 21888 then
      exact segment_sound _ 21760 128 Numeric0042_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 21888 128 Numeric0042_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
