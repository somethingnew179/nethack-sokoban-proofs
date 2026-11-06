import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0082_0_checked : (List.range' 41984 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0082_1_checked : (List.range' 42112 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0082_2_checked : (List.range' 42240 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0082_3_checked : (List.range' 42368 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0082_range (index : Nat) (lower : 41984 ≤ index) (upper : index < 42496) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 42240 then
    if cut : index < 42112 then
      exact segment_sound _ 41984 128 Numeric0082_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 42112 128 Numeric0082_1_checked index (by omega) (by omega)
  else
    if cut : index < 42368 then
      exact segment_sound _ 42240 128 Numeric0082_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 42368 128 Numeric0082_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
