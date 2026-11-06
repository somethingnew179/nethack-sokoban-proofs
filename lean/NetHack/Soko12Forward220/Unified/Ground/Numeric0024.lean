import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0024_0_checked : (List.range' 12288 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0024_1_checked : (List.range' 12416 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0024_2_checked : (List.range' 12544 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0024_3_checked : (List.range' 12672 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0024_range (index : Nat) (lower : 12288 ≤ index) (upper : index < 12800) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 12544 then
    if cut : index < 12416 then
      exact segment_sound _ 12288 128 Numeric0024_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 12416 128 Numeric0024_1_checked index (by omega) (by omega)
  else
    if cut : index < 12672 then
      exact segment_sound _ 12544 128 Numeric0024_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 12672 128 Numeric0024_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
