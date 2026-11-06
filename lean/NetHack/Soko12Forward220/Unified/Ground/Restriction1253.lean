import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1253_0_checked : (List.range' 641536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1253_1_checked : (List.range' 641664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1253_2_checked : (List.range' 641792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1253_3_checked : (List.range' 641920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1253_range (index : Nat) (lower : 641536 ≤ index) (upper : index < 642048) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 641792 then
    if cut : index < 641664 then
      exact segment_sound _ 641536 128 Restriction1253_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 641664 128 Restriction1253_1_checked index (by omega) (by omega)
  else
    if cut : index < 641920 then
      exact segment_sound _ 641792 128 Restriction1253_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 641920 128 Restriction1253_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
