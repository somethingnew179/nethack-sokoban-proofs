import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1458_0_checked : (List.range' 746496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1458_1_checked : (List.range' 746624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1458_2_checked : (List.range' 746752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1458_3_checked : (List.range' 746880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1458_range (index : Nat) (lower : 746496 ≤ index) (upper : index < 747008) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 746752 then
    if cut : index < 746624 then
      exact segment_sound _ 746496 128 Restriction1458_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 746624 128 Restriction1458_1_checked index (by omega) (by omega)
  else
    if cut : index < 746880 then
      exact segment_sound _ 746752 128 Restriction1458_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 746880 128 Restriction1458_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
