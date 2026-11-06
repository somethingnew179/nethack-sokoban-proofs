import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0150_0_checked : (List.range' 76800 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0150_1_checked : (List.range' 76928 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0150_2_checked : (List.range' 77056 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0150_3_checked : (List.range' 77184 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0150_range (index : Nat) (lower : 76800 ≤ index) (upper : index < 77312) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 77056 then
    if cut : index < 76928 then
      exact segment_sound _ 76800 128 Numeric0150_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 76928 128 Numeric0150_1_checked index (by omega) (by omega)
  else
    if cut : index < 77184 then
      exact segment_sound _ 77056 128 Numeric0150_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 77184 128 Numeric0150_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
