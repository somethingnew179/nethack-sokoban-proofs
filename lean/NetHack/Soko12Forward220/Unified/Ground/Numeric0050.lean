import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0050_0_checked : (List.range' 25600 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0050_1_checked : (List.range' 25728 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0050_2_checked : (List.range' 25856 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0050_3_checked : (List.range' 25984 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0050_range (index : Nat) (lower : 25600 ≤ index) (upper : index < 26112) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 25856 then
    if cut : index < 25728 then
      exact segment_sound _ 25600 128 Numeric0050_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 25728 128 Numeric0050_1_checked index (by omega) (by omega)
  else
    if cut : index < 25984 then
      exact segment_sound _ 25856 128 Numeric0050_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 25984 128 Numeric0050_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
