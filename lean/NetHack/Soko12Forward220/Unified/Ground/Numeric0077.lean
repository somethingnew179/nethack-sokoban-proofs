import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0077_0_checked : (List.range' 39424 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0077_1_checked : (List.range' 39552 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0077_2_checked : (List.range' 39680 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0077_3_checked : (List.range' 39808 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0077_range (index : Nat) (lower : 39424 ≤ index) (upper : index < 39936) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 39680 then
    if cut : index < 39552 then
      exact segment_sound _ 39424 128 Numeric0077_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 39552 128 Numeric0077_1_checked index (by omega) (by omega)
  else
    if cut : index < 39808 then
      exact segment_sound _ 39680 128 Numeric0077_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 39808 128 Numeric0077_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
