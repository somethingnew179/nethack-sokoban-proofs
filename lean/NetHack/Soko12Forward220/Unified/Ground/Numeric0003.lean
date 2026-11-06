import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0003_0_checked : (List.range' 1536 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0003_1_checked : (List.range' 1664 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0003_2_checked : (List.range' 1792 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0003_3_checked : (List.range' 1920 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0003_range (index : Nat) (lower : 1536 ≤ index) (upper : index < 2048) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 1792 then
    if cut : index < 1664 then
      exact segment_sound _ 1536 128 Numeric0003_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1664 128 Numeric0003_1_checked index (by omega) (by omega)
  else
    if cut : index < 1920 then
      exact segment_sound _ 1792 128 Numeric0003_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1920 128 Numeric0003_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
