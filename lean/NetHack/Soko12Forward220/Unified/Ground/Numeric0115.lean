import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0115_0_checked : (List.range' 58880 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0115_1_checked : (List.range' 59008 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0115_2_checked : (List.range' 59136 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0115_3_checked : (List.range' 59264 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0115_range (index : Nat) (lower : 58880 ≤ index) (upper : index < 59392) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 59136 then
    if cut : index < 59008 then
      exact segment_sound _ 58880 128 Numeric0115_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 59008 128 Numeric0115_1_checked index (by omega) (by omega)
  else
    if cut : index < 59264 then
      exact segment_sound _ 59136 128 Numeric0115_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 59264 128 Numeric0115_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
