import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0052_0_checked : (List.range' 26624 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0052_1_checked : (List.range' 26752 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0052_2_checked : (List.range' 26880 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0052_3_checked : (List.range' 27008 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0052_range (index : Nat) (lower : 26624 ≤ index) (upper : index < 27136) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 26880 then
    if cut : index < 26752 then
      exact segment_sound _ 26624 128 Numeric0052_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 26752 128 Numeric0052_1_checked index (by omega) (by omega)
  else
    if cut : index < 27008 then
      exact segment_sound _ 26880 128 Numeric0052_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 27008 128 Numeric0052_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
