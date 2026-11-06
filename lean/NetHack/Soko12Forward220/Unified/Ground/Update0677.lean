import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0677_0_checked : (List.range' 346624 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0677_1_checked : (List.range' 346752 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0677_2_checked : (List.range' 346880 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0677_3_checked : (List.range' 347008 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0677_range (index : Nat) (lower : 346624 ≤ index) (upper : index < 347136) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 346880 then
    if cut : index < 346752 then
      exact segment_sound _ 346624 128 Update0677_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 346752 128 Update0677_1_checked index (by omega) (by omega)
  else
    if cut : index < 347008 then
      exact segment_sound _ 346880 128 Update0677_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 347008 128 Update0677_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
