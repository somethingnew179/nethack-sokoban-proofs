import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1913_0_checked : (List.range' 979456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1913_1_checked : (List.range' 979584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1913_2_checked : (List.range' 979712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1913_3_checked : (List.range' 979840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1913_range (index : Nat) (lower : 979456 ≤ index) (upper : index < 979968) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 979712 then
    if cut : index < 979584 then
      exact segment_sound _ 979456 128 Restriction1913_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 979584 128 Restriction1913_1_checked index (by omega) (by omega)
  else
    if cut : index < 979840 then
      exact segment_sound _ 979712 128 Restriction1913_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 979840 128 Restriction1913_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
