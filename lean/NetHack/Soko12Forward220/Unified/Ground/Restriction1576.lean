import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1576_0_checked : (List.range' 806912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1576_1_checked : (List.range' 807040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1576_2_checked : (List.range' 807168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1576_3_checked : (List.range' 807296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1576_range (index : Nat) (lower : 806912 ≤ index) (upper : index < 807424) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 807168 then
    if cut : index < 807040 then
      exact segment_sound _ 806912 128 Restriction1576_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 807040 128 Restriction1576_1_checked index (by omega) (by omega)
  else
    if cut : index < 807296 then
      exact segment_sound _ 807168 128 Restriction1576_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 807296 128 Restriction1576_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
