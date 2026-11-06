import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0135_0_checked : (List.range' 69120 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0135_1_checked : (List.range' 69248 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0135_2_checked : (List.range' 69376 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0135_3_checked : (List.range' 69504 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0135_range (index : Nat) (lower : 69120 ≤ index) (upper : index < 69632) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 69376 then
    if cut : index < 69248 then
      exact segment_sound _ 69120 128 Numeric0135_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 69248 128 Numeric0135_1_checked index (by omega) (by omega)
  else
    if cut : index < 69504 then
      exact segment_sound _ 69376 128 Numeric0135_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 69504 128 Numeric0135_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
