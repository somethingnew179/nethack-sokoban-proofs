import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1331_0_checked : (List.range' 681472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1331_1_checked : (List.range' 681600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1331_2_checked : (List.range' 681728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1331_3_checked : (List.range' 681856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1331_range (index : Nat) (lower : 681472 ≤ index) (upper : index < 681984) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 681728 then
    if cut : index < 681600 then
      exact segment_sound _ 681472 128 Restriction1331_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 681600 128 Restriction1331_1_checked index (by omega) (by omega)
  else
    if cut : index < 681856 then
      exact segment_sound _ 681728 128 Restriction1331_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 681856 128 Restriction1331_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
