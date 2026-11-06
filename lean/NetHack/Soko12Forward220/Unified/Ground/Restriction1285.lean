import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1285_0_checked : (List.range' 657920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1285_1_checked : (List.range' 658048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1285_2_checked : (List.range' 658176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1285_3_checked : (List.range' 658304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1285_range (index : Nat) (lower : 657920 ≤ index) (upper : index < 658432) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 658176 then
    if cut : index < 658048 then
      exact segment_sound _ 657920 128 Restriction1285_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 658048 128 Restriction1285_1_checked index (by omega) (by omega)
  else
    if cut : index < 658304 then
      exact segment_sound _ 658176 128 Restriction1285_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 658304 128 Restriction1285_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
