import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1125_0_checked : (List.range' 576000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1125_1_checked : (List.range' 576128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1125_2_checked : (List.range' 576256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1125_3_checked : (List.range' 576384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1125_range (index : Nat) (lower : 576000 ≤ index) (upper : index < 576512) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 576256 then
    if cut : index < 576128 then
      exact segment_sound _ 576000 128 Restriction1125_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 576128 128 Restriction1125_1_checked index (by omega) (by omega)
  else
    if cut : index < 576384 then
      exact segment_sound _ 576256 128 Restriction1125_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 576384 128 Restriction1125_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
