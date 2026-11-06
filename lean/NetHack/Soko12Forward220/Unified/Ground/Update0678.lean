import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0678_0_checked : (List.range' 347136 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0678_1_checked : (List.range' 347264 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0678_2_checked : (List.range' 347392 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0678_3_checked : (List.range' 347520 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0678_range (index : Nat) (lower : 347136 ≤ index) (upper : index < 347648) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 347392 then
    if cut : index < 347264 then
      exact segment_sound _ 347136 128 Update0678_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 347264 128 Update0678_1_checked index (by omega) (by omega)
  else
    if cut : index < 347520 then
      exact segment_sound _ 347392 128 Update0678_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 347520 128 Update0678_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
