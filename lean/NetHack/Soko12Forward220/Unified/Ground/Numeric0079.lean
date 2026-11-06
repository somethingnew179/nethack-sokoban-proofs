import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0079_0_checked : (List.range' 40448 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0079_1_checked : (List.range' 40576 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0079_2_checked : (List.range' 40704 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0079_3_checked : (List.range' 40832 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0079_range (index : Nat) (lower : 40448 ≤ index) (upper : index < 40960) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 40704 then
    if cut : index < 40576 then
      exact segment_sound _ 40448 128 Numeric0079_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 40576 128 Numeric0079_1_checked index (by omega) (by omega)
  else
    if cut : index < 40832 then
      exact segment_sound _ 40704 128 Numeric0079_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 40832 128 Numeric0079_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
