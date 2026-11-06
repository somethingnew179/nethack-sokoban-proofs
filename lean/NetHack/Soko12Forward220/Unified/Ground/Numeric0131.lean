import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0131_0_checked : (List.range' 67072 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0131_1_checked : (List.range' 67200 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0131_2_checked : (List.range' 67328 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0131_3_checked : (List.range' 67456 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0131_range (index : Nat) (lower : 67072 ≤ index) (upper : index < 67584) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 67328 then
    if cut : index < 67200 then
      exact segment_sound _ 67072 128 Numeric0131_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 67200 128 Numeric0131_1_checked index (by omega) (by omega)
  else
    if cut : index < 67456 then
      exact segment_sound _ 67328 128 Numeric0131_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 67456 128 Numeric0131_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
