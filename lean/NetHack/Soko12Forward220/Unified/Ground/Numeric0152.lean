import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0152_0_checked : (List.range' 77824 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0152_1_checked : (List.range' 77952 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0152_2_checked : (List.range' 78080 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0152_3_checked : (List.range' 78208 112).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0152_range (index : Nat) (lower : 77824 ≤ index) (upper : index < 78320) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 78080 then
    if cut : index < 77952 then
      exact segment_sound _ 77824 128 Numeric0152_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 77952 128 Numeric0152_1_checked index (by omega) (by omega)
  else
    if cut : index < 78208 then
      exact segment_sound _ 78080 128 Numeric0152_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 78208 112 Numeric0152_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
