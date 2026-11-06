import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0139_0_checked : (List.range' 71168 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0139_1_checked : (List.range' 71296 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0139_2_checked : (List.range' 71424 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0139_3_checked : (List.range' 71552 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0139_range (index : Nat) (lower : 71168 ≤ index) (upper : index < 71680) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 71424 then
    if cut : index < 71296 then
      exact segment_sound _ 71168 128 Numeric0139_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 71296 128 Numeric0139_1_checked index (by omega) (by omega)
  else
    if cut : index < 71552 then
      exact segment_sound _ 71424 128 Numeric0139_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 71552 128 Numeric0139_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
