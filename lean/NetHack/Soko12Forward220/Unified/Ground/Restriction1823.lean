import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1823_0_checked : (List.range' 933376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1823_1_checked : (List.range' 933504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1823_2_checked : (List.range' 933632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1823_3_checked : (List.range' 933760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1823_range (index : Nat) (lower : 933376 ≤ index) (upper : index < 933888) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 933632 then
    if cut : index < 933504 then
      exact segment_sound _ 933376 128 Restriction1823_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 933504 128 Restriction1823_1_checked index (by omega) (by omega)
  else
    if cut : index < 933760 then
      exact segment_sound _ 933632 128 Restriction1823_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 933760 128 Restriction1823_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
