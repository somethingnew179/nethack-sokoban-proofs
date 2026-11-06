import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1276_0_checked : (List.range' 653312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1276_1_checked : (List.range' 653440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1276_2_checked : (List.range' 653568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1276_3_checked : (List.range' 653696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1276_range (index : Nat) (lower : 653312 ≤ index) (upper : index < 653824) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 653568 then
    if cut : index < 653440 then
      exact segment_sound _ 653312 128 Restriction1276_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 653440 128 Restriction1276_1_checked index (by omega) (by omega)
  else
    if cut : index < 653696 then
      exact segment_sound _ 653568 128 Restriction1276_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 653696 128 Restriction1276_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
