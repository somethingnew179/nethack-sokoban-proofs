import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1128_0_checked : (List.range' 577536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1128_1_checked : (List.range' 577664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1128_2_checked : (List.range' 577792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1128_3_checked : (List.range' 577920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1128_range (index : Nat) (lower : 577536 ≤ index) (upper : index < 578048) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 577792 then
    if cut : index < 577664 then
      exact segment_sound _ 577536 128 Restriction1128_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 577664 128 Restriction1128_1_checked index (by omega) (by omega)
  else
    if cut : index < 577920 then
      exact segment_sound _ 577792 128 Restriction1128_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 577920 128 Restriction1128_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
