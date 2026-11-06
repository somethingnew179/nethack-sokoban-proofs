import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0133_0_checked : (List.range' 68096 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0133_1_checked : (List.range' 68224 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0133_2_checked : (List.range' 68352 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0133_3_checked : (List.range' 68480 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0133_range (index : Nat) (lower : 68096 ≤ index) (upper : index < 68608) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 68352 then
    if cut : index < 68224 then
      exact segment_sound _ 68096 128 Numeric0133_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 68224 128 Numeric0133_1_checked index (by omega) (by omega)
  else
    if cut : index < 68480 then
      exact segment_sound _ 68352 128 Numeric0133_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 68480 128 Numeric0133_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
