import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2218_0_checked : (List.range' 1135616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2218_1_checked : (List.range' 1135744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2218_2_checked : (List.range' 1135872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2218_3_checked : (List.range' 1136000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2218_range (index : Nat) (lower : 1135616 ≤ index) (upper : index < 1136128) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1135872 then
    if cut : index < 1135744 then
      exact segment_sound _ 1135616 128 Restriction2218_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1135744 128 Restriction2218_1_checked index (by omega) (by omega)
  else
    if cut : index < 1136000 then
      exact segment_sound _ 1135872 128 Restriction2218_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1136000 128 Restriction2218_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
