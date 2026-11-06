import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1413_0_checked : (List.range' 723456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1413_1_checked : (List.range' 723584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1413_2_checked : (List.range' 723712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1413_3_checked : (List.range' 723840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1413_range (index : Nat) (lower : 723456 ≤ index) (upper : index < 723968) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 723712 then
    if cut : index < 723584 then
      exact segment_sound _ 723456 128 Restriction1413_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 723584 128 Restriction1413_1_checked index (by omega) (by omega)
  else
    if cut : index < 723840 then
      exact segment_sound _ 723712 128 Restriction1413_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 723840 128 Restriction1413_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
