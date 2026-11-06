import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0125_0_checked : (List.range' 64000 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0125_1_checked : (List.range' 64128 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0125_2_checked : (List.range' 64256 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0125_3_checked : (List.range' 64384 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0125_range (index : Nat) (lower : 64000 ≤ index) (upper : index < 64512) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 64256 then
    if cut : index < 64128 then
      exact segment_sound _ 64000 128 Numeric0125_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 64128 128 Numeric0125_1_checked index (by omega) (by omega)
  else
    if cut : index < 64384 then
      exact segment_sound _ 64256 128 Numeric0125_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 64384 128 Numeric0125_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
