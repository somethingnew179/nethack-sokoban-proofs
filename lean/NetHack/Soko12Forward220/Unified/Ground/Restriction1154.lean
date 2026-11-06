import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1154_0_checked : (List.range' 590848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1154_1_checked : (List.range' 590976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1154_2_checked : (List.range' 591104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1154_3_checked : (List.range' 591232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1154_range (index : Nat) (lower : 590848 ≤ index) (upper : index < 591360) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 591104 then
    if cut : index < 590976 then
      exact segment_sound _ 590848 128 Restriction1154_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 590976 128 Restriction1154_1_checked index (by omega) (by omega)
  else
    if cut : index < 591232 then
      exact segment_sound _ 591104 128 Restriction1154_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 591232 128 Restriction1154_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
