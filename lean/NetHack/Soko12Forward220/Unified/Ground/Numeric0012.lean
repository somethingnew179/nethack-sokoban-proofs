import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0012_0_checked : (List.range' 6144 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0012_1_checked : (List.range' 6272 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0012_2_checked : (List.range' 6400 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0012_3_checked : (List.range' 6528 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0012_range (index : Nat) (lower : 6144 ≤ index) (upper : index < 6656) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 6400 then
    if cut : index < 6272 then
      exact segment_sound _ 6144 128 Numeric0012_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 6272 128 Numeric0012_1_checked index (by omega) (by omega)
  else
    if cut : index < 6528 then
      exact segment_sound _ 6400 128 Numeric0012_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 6528 128 Numeric0012_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
