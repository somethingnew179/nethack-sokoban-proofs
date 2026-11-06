import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1897_0_checked : (List.range' 971264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1897_1_checked : (List.range' 971392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1897_2_checked : (List.range' 971520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1897_3_checked : (List.range' 971648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1897_range (index : Nat) (lower : 971264 ≤ index) (upper : index < 971776) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 971520 then
    if cut : index < 971392 then
      exact segment_sound _ 971264 128 Restriction1897_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 971392 128 Restriction1897_1_checked index (by omega) (by omega)
  else
    if cut : index < 971648 then
      exact segment_sound _ 971520 128 Restriction1897_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 971648 128 Restriction1897_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
