import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1340_0_checked : (List.range' 686080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1340_1_checked : (List.range' 686208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1340_2_checked : (List.range' 686336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1340_3_checked : (List.range' 686464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1340_range (index : Nat) (lower : 686080 ≤ index) (upper : index < 686592) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 686336 then
    if cut : index < 686208 then
      exact segment_sound _ 686080 128 Restriction1340_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 686208 128 Restriction1340_1_checked index (by omega) (by omega)
  else
    if cut : index < 686464 then
      exact segment_sound _ 686336 128 Restriction1340_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 686464 128 Restriction1340_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
