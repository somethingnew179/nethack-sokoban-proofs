import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1929_0_checked : (List.range' 987648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1929_1_checked : (List.range' 987776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1929_2_checked : (List.range' 987904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1929_3_checked : (List.range' 988032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1929_range (index : Nat) (lower : 987648 ≤ index) (upper : index < 988160) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 987904 then
    if cut : index < 987776 then
      exact segment_sound _ 987648 128 Restriction1929_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 987776 128 Restriction1929_1_checked index (by omega) (by omega)
  else
    if cut : index < 988032 then
      exact segment_sound _ 987904 128 Restriction1929_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 988032 128 Restriction1929_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
