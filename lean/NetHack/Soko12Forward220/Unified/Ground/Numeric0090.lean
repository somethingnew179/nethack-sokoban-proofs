import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0090_0_checked : (List.range' 46080 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0090_1_checked : (List.range' 46208 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0090_2_checked : (List.range' 46336 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0090_3_checked : (List.range' 46464 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0090_range (index : Nat) (lower : 46080 ≤ index) (upper : index < 46592) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 46336 then
    if cut : index < 46208 then
      exact segment_sound _ 46080 128 Numeric0090_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 46208 128 Numeric0090_1_checked index (by omega) (by omega)
  else
    if cut : index < 46464 then
      exact segment_sound _ 46336 128 Numeric0090_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 46464 128 Numeric0090_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
