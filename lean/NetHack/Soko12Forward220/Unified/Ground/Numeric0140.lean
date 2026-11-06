import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0140_0_checked : (List.range' 71680 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0140_1_checked : (List.range' 71808 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0140_2_checked : (List.range' 71936 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0140_3_checked : (List.range' 72064 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0140_range (index : Nat) (lower : 71680 ≤ index) (upper : index < 72192) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 71936 then
    if cut : index < 71808 then
      exact segment_sound _ 71680 128 Numeric0140_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 71808 128 Numeric0140_1_checked index (by omega) (by omega)
  else
    if cut : index < 72064 then
      exact segment_sound _ 71936 128 Numeric0140_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 72064 128 Numeric0140_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
