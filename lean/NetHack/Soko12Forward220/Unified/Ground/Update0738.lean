import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0738_0_checked : (List.range' 377856 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0738_1_checked : (List.range' 377984 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0738_2_checked : (List.range' 378112 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0738_3_checked : (List.range' 378240 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0738_range (index : Nat) (lower : 377856 ≤ index) (upper : index < 378368) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 378112 then
    if cut : index < 377984 then
      exact segment_sound _ 377856 128 Update0738_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 377984 128 Update0738_1_checked index (by omega) (by omega)
  else
    if cut : index < 378240 then
      exact segment_sound _ 378112 128 Update0738_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 378240 128 Update0738_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
