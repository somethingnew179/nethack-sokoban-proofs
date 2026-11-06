import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0011_0_checked : (List.range' 5632 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0011_1_checked : (List.range' 5760 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0011_2_checked : (List.range' 5888 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0011_3_checked : (List.range' 6016 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0011_range (index : Nat) (lower : 5632 ≤ index) (upper : index < 6144) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 5888 then
    if cut : index < 5760 then
      exact segment_sound _ 5632 128 Numeric0011_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 5760 128 Numeric0011_1_checked index (by omega) (by omega)
  else
    if cut : index < 6016 then
      exact segment_sound _ 5888 128 Numeric0011_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 6016 128 Numeric0011_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
