import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1660_0_checked : (List.range' 849920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1660_1_checked : (List.range' 850048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1660_2_checked : (List.range' 850176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1660_3_checked : (List.range' 850304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1660_range (index : Nat) (lower : 849920 ≤ index) (upper : index < 850432) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 850176 then
    if cut : index < 850048 then
      exact segment_sound _ 849920 128 Restriction1660_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 850048 128 Restriction1660_1_checked index (by omega) (by omega)
  else
    if cut : index < 850304 then
      exact segment_sound _ 850176 128 Restriction1660_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 850304 128 Restriction1660_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
