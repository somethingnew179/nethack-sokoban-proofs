import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0126_0_checked : (List.range' 64512 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0126_1_checked : (List.range' 64640 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0126_2_checked : (List.range' 64768 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0126_3_checked : (List.range' 64896 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0126_range (index : Nat) (lower : 64512 ≤ index) (upper : index < 65024) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 64768 then
    if cut : index < 64640 then
      exact segment_sound _ 64512 128 Numeric0126_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 64640 128 Numeric0126_1_checked index (by omega) (by omega)
  else
    if cut : index < 64896 then
      exact segment_sound _ 64768 128 Numeric0126_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 64896 128 Numeric0126_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
