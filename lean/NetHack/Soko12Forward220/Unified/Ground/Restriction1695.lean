import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1695_0_checked : (List.range' 867840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1695_1_checked : (List.range' 867968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1695_2_checked : (List.range' 868096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1695_3_checked : (List.range' 868224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1695_range (index : Nat) (lower : 867840 ≤ index) (upper : index < 868352) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 868096 then
    if cut : index < 867968 then
      exact segment_sound _ 867840 128 Restriction1695_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 867968 128 Restriction1695_1_checked index (by omega) (by omega)
  else
    if cut : index < 868224 then
      exact segment_sound _ 868096 128 Restriction1695_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 868224 128 Restriction1695_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
