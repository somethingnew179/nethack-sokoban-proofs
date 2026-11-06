import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0138_0_checked : (List.range' 70656 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0138_1_checked : (List.range' 70784 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0138_2_checked : (List.range' 70912 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0138_3_checked : (List.range' 71040 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0138_range (index : Nat) (lower : 70656 ≤ index) (upper : index < 71168) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 70912 then
    if cut : index < 70784 then
      exact segment_sound _ 70656 128 Numeric0138_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 70784 128 Numeric0138_1_checked index (by omega) (by omega)
  else
    if cut : index < 71040 then
      exact segment_sound _ 70912 128 Numeric0138_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 71040 128 Numeric0138_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
