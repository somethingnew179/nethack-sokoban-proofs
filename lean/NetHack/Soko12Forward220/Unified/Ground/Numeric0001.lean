import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0001_0_checked : (List.range' 512 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0001_1_checked : (List.range' 640 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0001_2_checked : (List.range' 768 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0001_3_checked : (List.range' 896 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0001_range (index : Nat) (lower : 512 ≤ index) (upper : index < 1024) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 768 then
    if cut : index < 640 then
      exact segment_sound _ 512 128 Numeric0001_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 640 128 Numeric0001_1_checked index (by omega) (by omega)
  else
    if cut : index < 896 then
      exact segment_sound _ 768 128 Numeric0001_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 896 128 Numeric0001_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
