import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0459_0_checked : (List.range' 235008 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0459_1_checked : (List.range' 235136 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0459_2_checked : (List.range' 235264 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0459_3_checked : (List.range' 235392 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0459_range (index : Nat) (lower : 235008 ≤ index) (upper : index < 235520) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 235264 then
    if cut : index < 235136 then
      exact segment_sound _ 235008 128 Update0459_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 235136 128 Update0459_1_checked index (by omega) (by omega)
  else
    if cut : index < 235392 then
      exact segment_sound _ 235264 128 Update0459_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 235392 128 Update0459_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
