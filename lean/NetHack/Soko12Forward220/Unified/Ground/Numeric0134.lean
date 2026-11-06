import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0134_0_checked : (List.range' 68608 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0134_1_checked : (List.range' 68736 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0134_2_checked : (List.range' 68864 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0134_3_checked : (List.range' 68992 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0134_range (index : Nat) (lower : 68608 ≤ index) (upper : index < 69120) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 68864 then
    if cut : index < 68736 then
      exact segment_sound _ 68608 128 Numeric0134_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 68736 128 Numeric0134_1_checked index (by omega) (by omega)
  else
    if cut : index < 68992 then
      exact segment_sound _ 68864 128 Numeric0134_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 68992 128 Numeric0134_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
