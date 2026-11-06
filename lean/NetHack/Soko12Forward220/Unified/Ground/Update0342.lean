import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0342_0_checked : (List.range' 175104 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0342_1_checked : (List.range' 175232 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0342_2_checked : (List.range' 175360 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0342_3_checked : (List.range' 175488 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0342_range (index : Nat) (lower : 175104 ≤ index) (upper : index < 175616) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 175360 then
    if cut : index < 175232 then
      exact segment_sound _ 175104 128 Update0342_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 175232 128 Update0342_1_checked index (by omega) (by omega)
  else
    if cut : index < 175488 then
      exact segment_sound _ 175360 128 Update0342_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 175488 128 Update0342_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
