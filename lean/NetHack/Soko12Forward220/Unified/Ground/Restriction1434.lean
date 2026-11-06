import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1434_0_checked : (List.range' 734208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1434_1_checked : (List.range' 734336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1434_2_checked : (List.range' 734464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1434_3_checked : (List.range' 734592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1434_range (index : Nat) (lower : 734208 ≤ index) (upper : index < 734720) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 734464 then
    if cut : index < 734336 then
      exact segment_sound _ 734208 128 Restriction1434_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 734336 128 Restriction1434_1_checked index (by omega) (by omega)
  else
    if cut : index < 734592 then
      exact segment_sound _ 734464 128 Restriction1434_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 734592 128 Restriction1434_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
