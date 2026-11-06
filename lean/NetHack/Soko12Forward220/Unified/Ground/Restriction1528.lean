import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1528_0_checked : (List.range' 782336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1528_1_checked : (List.range' 782464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1528_2_checked : (List.range' 782592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1528_3_checked : (List.range' 782720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1528_range (index : Nat) (lower : 782336 ≤ index) (upper : index < 782848) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 782592 then
    if cut : index < 782464 then
      exact segment_sound _ 782336 128 Restriction1528_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 782464 128 Restriction1528_1_checked index (by omega) (by omega)
  else
    if cut : index < 782720 then
      exact segment_sound _ 782592 128 Restriction1528_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 782720 128 Restriction1528_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
