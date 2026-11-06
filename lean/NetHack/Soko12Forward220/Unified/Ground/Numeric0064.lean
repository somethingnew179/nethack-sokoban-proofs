import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0064_0_checked : (List.range' 32768 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0064_1_checked : (List.range' 32896 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0064_2_checked : (List.range' 33024 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0064_3_checked : (List.range' 33152 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0064_range (index : Nat) (lower : 32768 ≤ index) (upper : index < 33280) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 33024 then
    if cut : index < 32896 then
      exact segment_sound _ 32768 128 Numeric0064_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 32896 128 Numeric0064_1_checked index (by omega) (by omega)
  else
    if cut : index < 33152 then
      exact segment_sound _ 33024 128 Numeric0064_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 33152 128 Numeric0064_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
