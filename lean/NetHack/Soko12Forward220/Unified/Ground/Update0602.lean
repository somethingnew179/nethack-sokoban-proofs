import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0602_0_checked : (List.range' 308224 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0602_1_checked : (List.range' 308352 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0602_2_checked : (List.range' 308480 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0602_3_checked : (List.range' 308608 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0602_range (index : Nat) (lower : 308224 ≤ index) (upper : index < 308736) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 308480 then
    if cut : index < 308352 then
      exact segment_sound _ 308224 128 Update0602_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 308352 128 Update0602_1_checked index (by omega) (by omega)
  else
    if cut : index < 308608 then
      exact segment_sound _ 308480 128 Update0602_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 308608 128 Update0602_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
