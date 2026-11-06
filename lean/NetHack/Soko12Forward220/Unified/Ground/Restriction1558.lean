import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1558_0_checked : (List.range' 797696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1558_1_checked : (List.range' 797824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1558_2_checked : (List.range' 797952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1558_3_checked : (List.range' 798080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1558_range (index : Nat) (lower : 797696 ≤ index) (upper : index < 798208) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 797952 then
    if cut : index < 797824 then
      exact segment_sound _ 797696 128 Restriction1558_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 797824 128 Restriction1558_1_checked index (by omega) (by omega)
  else
    if cut : index < 798080 then
      exact segment_sound _ 797952 128 Restriction1558_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 798080 128 Restriction1558_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
