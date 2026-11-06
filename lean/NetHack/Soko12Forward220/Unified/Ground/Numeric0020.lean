import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0020_0_checked : (List.range' 10240 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0020_1_checked : (List.range' 10368 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0020_2_checked : (List.range' 10496 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0020_3_checked : (List.range' 10624 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0020_range (index : Nat) (lower : 10240 ≤ index) (upper : index < 10752) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 10496 then
    if cut : index < 10368 then
      exact segment_sound _ 10240 128 Numeric0020_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 10368 128 Numeric0020_1_checked index (by omega) (by omega)
  else
    if cut : index < 10624 then
      exact segment_sound _ 10496 128 Numeric0020_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 10624 128 Numeric0020_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
