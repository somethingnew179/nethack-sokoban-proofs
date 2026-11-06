import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0029_0_checked : (List.range' 14848 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0029_1_checked : (List.range' 14976 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0029_2_checked : (List.range' 15104 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0029_3_checked : (List.range' 15232 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0029_range (index : Nat) (lower : 14848 ≤ index) (upper : index < 15360) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 15104 then
    if cut : index < 14976 then
      exact segment_sound _ 14848 128 Numeric0029_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 14976 128 Numeric0029_1_checked index (by omega) (by omega)
  else
    if cut : index < 15232 then
      exact segment_sound _ 15104 128 Numeric0029_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 15232 128 Numeric0029_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
