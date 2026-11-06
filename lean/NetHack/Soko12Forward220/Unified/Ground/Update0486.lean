import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0486_0_checked : (List.range' 248832 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0486_1_checked : (List.range' 248960 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0486_2_checked : (List.range' 249088 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0486_3_checked : (List.range' 249216 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0486_range (index : Nat) (lower : 248832 ≤ index) (upper : index < 249344) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 249088 then
    if cut : index < 248960 then
      exact segment_sound _ 248832 128 Update0486_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 248960 128 Update0486_1_checked index (by omega) (by omega)
  else
    if cut : index < 249216 then
      exact segment_sound _ 249088 128 Update0486_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 249216 128 Update0486_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
