import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1024_0_checked : (List.range' 524288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1024_1_checked : (List.range' 524416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1024_2_checked : (List.range' 524544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1024_3_checked : (List.range' 524672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1024_range (index : Nat) (lower : 524288 ≤ index) (upper : index < 524800) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 524544 then
    if cut : index < 524416 then
      exact segment_sound _ 524288 128 Restriction1024_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 524416 128 Restriction1024_1_checked index (by omega) (by omega)
  else
    if cut : index < 524672 then
      exact segment_sound _ 524544 128 Restriction1024_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 524672 128 Restriction1024_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
