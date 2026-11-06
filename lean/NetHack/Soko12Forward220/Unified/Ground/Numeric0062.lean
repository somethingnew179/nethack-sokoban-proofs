import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0062_0_checked : (List.range' 31744 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0062_1_checked : (List.range' 31872 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0062_2_checked : (List.range' 32000 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0062_3_checked : (List.range' 32128 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0062_range (index : Nat) (lower : 31744 ≤ index) (upper : index < 32256) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 32000 then
    if cut : index < 31872 then
      exact segment_sound _ 31744 128 Numeric0062_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 31872 128 Numeric0062_1_checked index (by omega) (by omega)
  else
    if cut : index < 32128 then
      exact segment_sound _ 32000 128 Numeric0062_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 32128 128 Numeric0062_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
