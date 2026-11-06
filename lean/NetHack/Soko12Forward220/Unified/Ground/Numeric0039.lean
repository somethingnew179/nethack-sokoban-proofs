import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0039_0_checked : (List.range' 19968 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0039_1_checked : (List.range' 20096 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0039_2_checked : (List.range' 20224 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0039_3_checked : (List.range' 20352 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0039_range (index : Nat) (lower : 19968 ≤ index) (upper : index < 20480) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 20224 then
    if cut : index < 20096 then
      exact segment_sound _ 19968 128 Numeric0039_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 20096 128 Numeric0039_1_checked index (by omega) (by omega)
  else
    if cut : index < 20352 then
      exact segment_sound _ 20224 128 Numeric0039_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 20352 128 Numeric0039_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
