import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0461_0_checked : (List.range' 236032 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0461_1_checked : (List.range' 236160 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0461_2_checked : (List.range' 236288 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0461_3_checked : (List.range' 236416 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0461_range (index : Nat) (lower : 236032 ≤ index) (upper : index < 236544) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 236288 then
    if cut : index < 236160 then
      exact segment_sound _ 236032 128 Update0461_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 236160 128 Update0461_1_checked index (by omega) (by omega)
  else
    if cut : index < 236416 then
      exact segment_sound _ 236288 128 Update0461_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 236416 128 Update0461_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
