import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1182_0_checked : (List.range' 605184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1182_1_checked : (List.range' 605312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1182_2_checked : (List.range' 605440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1182_3_checked : (List.range' 605568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1182_range (index : Nat) (lower : 605184 ≤ index) (upper : index < 605696) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 605440 then
    if cut : index < 605312 then
      exact segment_sound _ 605184 128 Restriction1182_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 605312 128 Restriction1182_1_checked index (by omega) (by omega)
  else
    if cut : index < 605568 then
      exact segment_sound _ 605440 128 Restriction1182_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 605568 128 Restriction1182_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
