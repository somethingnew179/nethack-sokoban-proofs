import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0211_0_checked : (List.range' 108032 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0211_1_checked : (List.range' 108160 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0211_2_checked : (List.range' 108288 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0211_3_checked : (List.range' 108416 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0211_range (index : Nat) (lower : 108032 ≤ index) (upper : index < 108544) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 108288 then
    if cut : index < 108160 then
      exact segment_sound _ 108032 128 Update0211_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 108160 128 Update0211_1_checked index (by omega) (by omega)
  else
    if cut : index < 108416 then
      exact segment_sound _ 108288 128 Update0211_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 108416 128 Update0211_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
