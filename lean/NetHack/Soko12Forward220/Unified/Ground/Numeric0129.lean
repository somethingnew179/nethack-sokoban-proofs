import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0129_0_checked : (List.range' 66048 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0129_1_checked : (List.range' 66176 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0129_2_checked : (List.range' 66304 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0129_3_checked : (List.range' 66432 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0129_range (index : Nat) (lower : 66048 ≤ index) (upper : index < 66560) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 66304 then
    if cut : index < 66176 then
      exact segment_sound _ 66048 128 Numeric0129_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 66176 128 Numeric0129_1_checked index (by omega) (by omega)
  else
    if cut : index < 66432 then
      exact segment_sound _ 66304 128 Numeric0129_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 66432 128 Numeric0129_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
