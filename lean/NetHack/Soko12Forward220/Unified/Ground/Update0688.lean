import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0688_0_checked : (List.range' 352256 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0688_1_checked : (List.range' 352384 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0688_2_checked : (List.range' 352512 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0688_3_checked : (List.range' 352640 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0688_range (index : Nat) (lower : 352256 ≤ index) (upper : index < 352768) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 352512 then
    if cut : index < 352384 then
      exact segment_sound _ 352256 128 Update0688_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 352384 128 Update0688_1_checked index (by omega) (by omega)
  else
    if cut : index < 352640 then
      exact segment_sound _ 352512 128 Update0688_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 352640 128 Update0688_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
