import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0009_0_checked : (List.range' 4608 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0009_1_checked : (List.range' 4736 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0009_2_checked : (List.range' 4864 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0009_3_checked : (List.range' 4992 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0009_range (index : Nat) (lower : 4608 ≤ index) (upper : index < 5120) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 4864 then
    if cut : index < 4736 then
      exact segment_sound _ 4608 128 Numeric0009_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 4736 128 Numeric0009_1_checked index (by omega) (by omega)
  else
    if cut : index < 4992 then
      exact segment_sound _ 4864 128 Numeric0009_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 4992 128 Numeric0009_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
