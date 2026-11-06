import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0630_0_checked : (List.range' 322560 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0630_1_checked : (List.range' 322688 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0630_2_checked : (List.range' 322816 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0630_3_checked : (List.range' 322944 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0630_range (index : Nat) (lower : 322560 ≤ index) (upper : index < 323072) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 322816 then
    if cut : index < 322688 then
      exact segment_sound _ 322560 128 Update0630_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 322688 128 Update0630_1_checked index (by omega) (by omega)
  else
    if cut : index < 322944 then
      exact segment_sound _ 322816 128 Update0630_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 322944 128 Update0630_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
