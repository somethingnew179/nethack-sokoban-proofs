import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0021_0_checked : (List.range' 10752 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0021_1_checked : (List.range' 10880 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0021_2_checked : (List.range' 11008 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0021_3_checked : (List.range' 11136 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0021_range (index : Nat) (lower : 10752 ≤ index) (upper : index < 11264) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 11008 then
    if cut : index < 10880 then
      exact segment_sound _ 10752 128 Numeric0021_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 10880 128 Numeric0021_1_checked index (by omega) (by omega)
  else
    if cut : index < 11136 then
      exact segment_sound _ 11008 128 Numeric0021_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 11136 128 Numeric0021_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
