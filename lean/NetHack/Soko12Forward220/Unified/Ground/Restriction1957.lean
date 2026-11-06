import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1957_0_checked : (List.range' 1001984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1957_1_checked : (List.range' 1002112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1957_2_checked : (List.range' 1002240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1957_3_checked : (List.range' 1002368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1957_range (index : Nat) (lower : 1001984 ≤ index) (upper : index < 1002496) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1002240 then
    if cut : index < 1002112 then
      exact segment_sound _ 1001984 128 Restriction1957_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1002112 128 Restriction1957_1_checked index (by omega) (by omega)
  else
    if cut : index < 1002368 then
      exact segment_sound _ 1002240 128 Restriction1957_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1002368 128 Restriction1957_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
