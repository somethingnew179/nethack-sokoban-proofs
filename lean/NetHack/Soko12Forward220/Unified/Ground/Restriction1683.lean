import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1683_0_checked : (List.range' 861696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1683_1_checked : (List.range' 861824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1683_2_checked : (List.range' 861952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1683_3_checked : (List.range' 862080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1683_range (index : Nat) (lower : 861696 ≤ index) (upper : index < 862208) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 861952 then
    if cut : index < 861824 then
      exact segment_sound _ 861696 128 Restriction1683_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 861824 128 Restriction1683_1_checked index (by omega) (by omega)
  else
    if cut : index < 862080 then
      exact segment_sound _ 861952 128 Restriction1683_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 862080 128 Restriction1683_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
