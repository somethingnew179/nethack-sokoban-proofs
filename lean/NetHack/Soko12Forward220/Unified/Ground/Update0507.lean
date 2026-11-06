import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0507_0_checked : (List.range' 259584 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0507_1_checked : (List.range' 259712 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0507_2_checked : (List.range' 259840 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0507_3_checked : (List.range' 259968 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0507_range (index : Nat) (lower : 259584 ≤ index) (upper : index < 260096) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 259840 then
    if cut : index < 259712 then
      exact segment_sound _ 259584 128 Update0507_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 259712 128 Update0507_1_checked index (by omega) (by omega)
  else
    if cut : index < 259968 then
      exact segment_sound _ 259840 128 Update0507_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 259968 128 Update0507_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
