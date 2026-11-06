import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1405_0_checked : (List.range' 719360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1405_1_checked : (List.range' 719488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1405_2_checked : (List.range' 719616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1405_3_checked : (List.range' 719744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1405_range (index : Nat) (lower : 719360 ≤ index) (upper : index < 719872) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 719616 then
    if cut : index < 719488 then
      exact segment_sound _ 719360 128 Restriction1405_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 719488 128 Restriction1405_1_checked index (by omega) (by omega)
  else
    if cut : index < 719744 then
      exact segment_sound _ 719616 128 Restriction1405_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 719744 128 Restriction1405_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
