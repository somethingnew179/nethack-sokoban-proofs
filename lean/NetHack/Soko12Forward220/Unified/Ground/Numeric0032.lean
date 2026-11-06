import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0032_0_checked : (List.range' 16384 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0032_1_checked : (List.range' 16512 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0032_2_checked : (List.range' 16640 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0032_3_checked : (List.range' 16768 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0032_range (index : Nat) (lower : 16384 ≤ index) (upper : index < 16896) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 16640 then
    if cut : index < 16512 then
      exact segment_sound _ 16384 128 Numeric0032_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 16512 128 Numeric0032_1_checked index (by omega) (by omega)
  else
    if cut : index < 16768 then
      exact segment_sound _ 16640 128 Numeric0032_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 16768 128 Numeric0032_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
