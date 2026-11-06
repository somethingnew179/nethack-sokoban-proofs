import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0095_0_checked : (List.range' 48640 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0095_1_checked : (List.range' 48768 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0095_2_checked : (List.range' 48896 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0095_3_checked : (List.range' 49024 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0095_range (index : Nat) (lower : 48640 ≤ index) (upper : index < 49152) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 48896 then
    if cut : index < 48768 then
      exact segment_sound _ 48640 128 Numeric0095_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 48768 128 Numeric0095_1_checked index (by omega) (by omega)
  else
    if cut : index < 49024 then
      exact segment_sound _ 48896 128 Numeric0095_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 49024 128 Numeric0095_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
