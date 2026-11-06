import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1022_0_checked : (List.range' 523264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1022_1_checked : (List.range' 523392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1022_2_checked : (List.range' 523520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1022_3_checked : (List.range' 523648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1022_range (index : Nat) (lower : 523264 ≤ index) (upper : index < 523776) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 523520 then
    if cut : index < 523392 then
      exact segment_sound _ 523264 128 Restriction1022_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 523392 128 Restriction1022_1_checked index (by omega) (by omega)
  else
    if cut : index < 523648 then
      exact segment_sound _ 523520 128 Restriction1022_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 523648 128 Restriction1022_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
