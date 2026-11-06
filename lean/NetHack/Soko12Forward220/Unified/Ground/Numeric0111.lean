import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0111_0_checked : (List.range' 56832 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0111_1_checked : (List.range' 56960 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0111_2_checked : (List.range' 57088 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0111_3_checked : (List.range' 57216 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0111_range (index : Nat) (lower : 56832 ≤ index) (upper : index < 57344) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 57088 then
    if cut : index < 56960 then
      exact segment_sound _ 56832 128 Numeric0111_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 56960 128 Numeric0111_1_checked index (by omega) (by omega)
  else
    if cut : index < 57216 then
      exact segment_sound _ 57088 128 Numeric0111_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 57216 128 Numeric0111_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
