import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0523_0_checked : (List.range' 267776 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0523_1_checked : (List.range' 267904 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0523_2_checked : (List.range' 268032 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0523_3_checked : (List.range' 268160 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0523_range (index : Nat) (lower : 267776 ≤ index) (upper : index < 268288) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 268032 then
    if cut : index < 267904 then
      exact segment_sound _ 267776 128 Update0523_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 267904 128 Update0523_1_checked index (by omega) (by omega)
  else
    if cut : index < 268160 then
      exact segment_sound _ 268032 128 Update0523_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 268160 128 Update0523_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
