import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2281_0_checked : (List.range' 1167872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2281_1_checked : (List.range' 1168000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2281_2_checked : (List.range' 1168128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2281_3_checked : (List.range' 1168256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2281_range (index : Nat) (lower : 1167872 ≤ index) (upper : index < 1168384) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1168128 then
    if cut : index < 1168000 then
      exact segment_sound _ 1167872 128 Restriction2281_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1168000 128 Restriction2281_1_checked index (by omega) (by omega)
  else
    if cut : index < 1168256 then
      exact segment_sound _ 1168128 128 Restriction2281_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1168256 128 Restriction2281_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
