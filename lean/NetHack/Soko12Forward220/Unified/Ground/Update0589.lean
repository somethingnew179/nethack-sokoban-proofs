import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0589_0_checked : (List.range' 301568 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0589_1_checked : (List.range' 301696 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0589_2_checked : (List.range' 301824 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0589_3_checked : (List.range' 301952 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0589_range (index : Nat) (lower : 301568 ≤ index) (upper : index < 302080) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 301824 then
    if cut : index < 301696 then
      exact segment_sound _ 301568 128 Update0589_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 301696 128 Update0589_1_checked index (by omega) (by omega)
  else
    if cut : index < 301952 then
      exact segment_sound _ 301824 128 Update0589_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 301952 128 Update0589_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
