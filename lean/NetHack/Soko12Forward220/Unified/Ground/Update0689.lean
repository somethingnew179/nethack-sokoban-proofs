import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0689_0_checked : (List.range' 352768 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0689_1_checked : (List.range' 352896 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0689_2_checked : (List.range' 353024 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0689_3_checked : (List.range' 353152 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0689_range (index : Nat) (lower : 352768 ≤ index) (upper : index < 353280) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 353024 then
    if cut : index < 352896 then
      exact segment_sound _ 352768 128 Update0689_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 352896 128 Update0689_1_checked index (by omega) (by omega)
  else
    if cut : index < 353152 then
      exact segment_sound _ 353024 128 Update0689_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 353152 128 Update0689_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
