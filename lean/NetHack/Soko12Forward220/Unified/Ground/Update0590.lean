import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0590_0_checked : (List.range' 302080 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0590_1_checked : (List.range' 302208 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0590_2_checked : (List.range' 302336 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0590_3_checked : (List.range' 302464 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0590_range (index : Nat) (lower : 302080 ≤ index) (upper : index < 302592) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 302336 then
    if cut : index < 302208 then
      exact segment_sound _ 302080 128 Update0590_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 302208 128 Update0590_1_checked index (by omega) (by omega)
  else
    if cut : index < 302464 then
      exact segment_sound _ 302336 128 Update0590_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 302464 128 Update0590_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
