import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1278_0_checked : (List.range' 654336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1278_1_checked : (List.range' 654464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1278_2_checked : (List.range' 654592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1278_3_checked : (List.range' 654720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1278_range (index : Nat) (lower : 654336 ≤ index) (upper : index < 654848) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 654592 then
    if cut : index < 654464 then
      exact segment_sound _ 654336 128 Restriction1278_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 654464 128 Restriction1278_1_checked index (by omega) (by omega)
  else
    if cut : index < 654720 then
      exact segment_sound _ 654592 128 Restriction1278_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 654720 128 Restriction1278_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
