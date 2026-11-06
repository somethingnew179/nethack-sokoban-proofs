import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0472_0_checked : (List.range' 241664 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0472_1_checked : (List.range' 241792 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0472_2_checked : (List.range' 241920 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0472_3_checked : (List.range' 242048 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0472_range (index : Nat) (lower : 241664 ≤ index) (upper : index < 242176) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 241920 then
    if cut : index < 241792 then
      exact segment_sound _ 241664 128 Update0472_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 241792 128 Update0472_1_checked index (by omega) (by omega)
  else
    if cut : index < 242048 then
      exact segment_sound _ 241920 128 Update0472_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 242048 128 Update0472_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
