import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1079_0_checked : (List.range' 552448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1079_1_checked : (List.range' 552576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1079_2_checked : (List.range' 552704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1079_3_checked : (List.range' 552832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1079_range (index : Nat) (lower : 552448 ≤ index) (upper : index < 552960) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 552704 then
    if cut : index < 552576 then
      exact segment_sound _ 552448 128 Restriction1079_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 552576 128 Restriction1079_1_checked index (by omega) (by omega)
  else
    if cut : index < 552832 then
      exact segment_sound _ 552704 128 Restriction1079_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 552832 128 Restriction1079_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
