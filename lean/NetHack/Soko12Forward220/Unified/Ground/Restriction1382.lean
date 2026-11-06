import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1382_0_checked : (List.range' 707584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1382_1_checked : (List.range' 707712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1382_2_checked : (List.range' 707840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1382_3_checked : (List.range' 707968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1382_range (index : Nat) (lower : 707584 ≤ index) (upper : index < 708096) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 707840 then
    if cut : index < 707712 then
      exact segment_sound _ 707584 128 Restriction1382_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 707712 128 Restriction1382_1_checked index (by omega) (by omega)
  else
    if cut : index < 707968 then
      exact segment_sound _ 707840 128 Restriction1382_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 707968 128 Restriction1382_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
