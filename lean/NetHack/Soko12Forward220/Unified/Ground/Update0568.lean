import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0568_0_checked : (List.range' 290816 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0568_1_checked : (List.range' 290944 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0568_2_checked : (List.range' 291072 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0568_3_checked : (List.range' 291200 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0568_range (index : Nat) (lower : 290816 ≤ index) (upper : index < 291328) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 291072 then
    if cut : index < 290944 then
      exact segment_sound _ 290816 128 Update0568_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 290944 128 Update0568_1_checked index (by omega) (by omega)
  else
    if cut : index < 291200 then
      exact segment_sound _ 291072 128 Update0568_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 291200 128 Update0568_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
