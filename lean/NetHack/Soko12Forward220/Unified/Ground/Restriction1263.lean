import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1263_0_checked : (List.range' 646656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1263_1_checked : (List.range' 646784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1263_2_checked : (List.range' 646912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1263_3_checked : (List.range' 647040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1263_range (index : Nat) (lower : 646656 ≤ index) (upper : index < 647168) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 646912 then
    if cut : index < 646784 then
      exact segment_sound _ 646656 128 Restriction1263_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 646784 128 Restriction1263_1_checked index (by omega) (by omega)
  else
    if cut : index < 647040 then
      exact segment_sound _ 646912 128 Restriction1263_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 647040 128 Restriction1263_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
