import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1779_0_checked : (List.range' 910848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1779_1_checked : (List.range' 910976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1779_2_checked : (List.range' 911104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1779_3_checked : (List.range' 911232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1779_range (index : Nat) (lower : 910848 ≤ index) (upper : index < 911360) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 911104 then
    if cut : index < 910976 then
      exact segment_sound _ 910848 128 Restriction1779_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 910976 128 Restriction1779_1_checked index (by omega) (by omega)
  else
    if cut : index < 911232 then
      exact segment_sound _ 911104 128 Restriction1779_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 911232 128 Restriction1779_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
