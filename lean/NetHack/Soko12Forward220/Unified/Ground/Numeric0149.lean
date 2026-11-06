import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0149_0_checked : (List.range' 76288 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0149_1_checked : (List.range' 76416 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0149_2_checked : (List.range' 76544 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0149_3_checked : (List.range' 76672 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0149_range (index : Nat) (lower : 76288 ≤ index) (upper : index < 76800) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 76544 then
    if cut : index < 76416 then
      exact segment_sound _ 76288 128 Numeric0149_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 76416 128 Numeric0149_1_checked index (by omega) (by omega)
  else
    if cut : index < 76672 then
      exact segment_sound _ 76544 128 Numeric0149_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 76672 128 Numeric0149_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
