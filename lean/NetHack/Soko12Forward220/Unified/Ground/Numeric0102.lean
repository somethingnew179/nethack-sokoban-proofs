import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0102_0_checked : (List.range' 52224 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0102_1_checked : (List.range' 52352 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0102_2_checked : (List.range' 52480 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0102_3_checked : (List.range' 52608 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0102_range (index : Nat) (lower : 52224 ≤ index) (upper : index < 52736) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 52480 then
    if cut : index < 52352 then
      exact segment_sound _ 52224 128 Numeric0102_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 52352 128 Numeric0102_1_checked index (by omega) (by omega)
  else
    if cut : index < 52608 then
      exact segment_sound _ 52480 128 Numeric0102_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 52608 128 Numeric0102_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
