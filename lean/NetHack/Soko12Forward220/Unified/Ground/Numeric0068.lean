import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0068_0_checked : (List.range' 34816 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0068_1_checked : (List.range' 34944 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0068_2_checked : (List.range' 35072 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0068_3_checked : (List.range' 35200 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0068_range (index : Nat) (lower : 34816 ≤ index) (upper : index < 35328) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 35072 then
    if cut : index < 34944 then
      exact segment_sound _ 34816 128 Numeric0068_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 34944 128 Numeric0068_1_checked index (by omega) (by omega)
  else
    if cut : index < 35200 then
      exact segment_sound _ 35072 128 Numeric0068_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 35200 128 Numeric0068_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
