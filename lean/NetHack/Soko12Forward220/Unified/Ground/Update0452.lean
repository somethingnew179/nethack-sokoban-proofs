import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0452_0_checked : (List.range' 231424 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0452_1_checked : (List.range' 231552 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0452_2_checked : (List.range' 231680 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0452_3_checked : (List.range' 231808 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0452_range (index : Nat) (lower : 231424 ≤ index) (upper : index < 231936) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 231680 then
    if cut : index < 231552 then
      exact segment_sound _ 231424 128 Update0452_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 231552 128 Update0452_1_checked index (by omega) (by omega)
  else
    if cut : index < 231808 then
      exact segment_sound _ 231680 128 Update0452_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 231808 128 Update0452_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
