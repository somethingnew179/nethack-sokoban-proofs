import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0044_0_checked : (List.range' 22528 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0044_1_checked : (List.range' 22656 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0044_2_checked : (List.range' 22784 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0044_3_checked : (List.range' 22912 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0044_range (index : Nat) (lower : 22528 ≤ index) (upper : index < 23040) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 22784 then
    if cut : index < 22656 then
      exact segment_sound _ 22528 128 Numeric0044_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 22656 128 Numeric0044_1_checked index (by omega) (by omega)
  else
    if cut : index < 22912 then
      exact segment_sound _ 22784 128 Numeric0044_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 22912 128 Numeric0044_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
