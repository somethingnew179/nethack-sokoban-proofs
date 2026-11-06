import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0274_0_checked : (List.range' 140288 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0274_1_checked : (List.range' 140416 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0274_2_checked : (List.range' 140544 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0274_3_checked : (List.range' 140672 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0274_range (index : Nat) (lower : 140288 ≤ index) (upper : index < 140800) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 140544 then
    if cut : index < 140416 then
      exact segment_sound _ 140288 128 Update0274_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 140416 128 Update0274_1_checked index (by omega) (by omega)
  else
    if cut : index < 140672 then
      exact segment_sound _ 140544 128 Update0274_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 140672 128 Update0274_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
