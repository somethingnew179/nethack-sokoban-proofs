import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0071_0_checked : (List.range' 36352 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0071_1_checked : (List.range' 36480 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0071_2_checked : (List.range' 36608 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0071_3_checked : (List.range' 36736 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0071_range (index : Nat) (lower : 36352 ≤ index) (upper : index < 36864) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 36608 then
    if cut : index < 36480 then
      exact segment_sound _ 36352 128 Numeric0071_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 36480 128 Numeric0071_1_checked index (by omega) (by omega)
  else
    if cut : index < 36736 then
      exact segment_sound _ 36608 128 Numeric0071_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 36736 128 Numeric0071_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
