import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0005_0_checked : (List.range' 2560 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0005_1_checked : (List.range' 2688 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0005_2_checked : (List.range' 2816 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0005_3_checked : (List.range' 2944 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0005_range (index : Nat) (lower : 2560 ≤ index) (upper : index < 3072) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 2816 then
    if cut : index < 2688 then
      exact segment_sound _ 2560 128 Numeric0005_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 2688 128 Numeric0005_1_checked index (by omega) (by omega)
  else
    if cut : index < 2944 then
      exact segment_sound _ 2816 128 Numeric0005_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 2944 128 Numeric0005_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
