import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0067_0_checked : (List.range' 34304 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0067_1_checked : (List.range' 34432 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0067_2_checked : (List.range' 34560 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0067_3_checked : (List.range' 34688 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0067_range (index : Nat) (lower : 34304 ≤ index) (upper : index < 34816) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 34560 then
    if cut : index < 34432 then
      exact segment_sound _ 34304 128 Numeric0067_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 34432 128 Numeric0067_1_checked index (by omega) (by omega)
  else
    if cut : index < 34688 then
      exact segment_sound _ 34560 128 Numeric0067_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 34688 128 Numeric0067_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
