import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1635_0_checked : (List.range' 837120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1635_1_checked : (List.range' 837248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1635_2_checked : (List.range' 837376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1635_3_checked : (List.range' 837504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1635_range (index : Nat) (lower : 837120 ≤ index) (upper : index < 837632) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 837376 then
    if cut : index < 837248 then
      exact segment_sound _ 837120 128 Restriction1635_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 837248 128 Restriction1635_1_checked index (by omega) (by omega)
  else
    if cut : index < 837504 then
      exact segment_sound _ 837376 128 Restriction1635_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 837504 128 Restriction1635_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
