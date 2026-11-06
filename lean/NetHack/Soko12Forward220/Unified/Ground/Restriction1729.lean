import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1729_0_checked : (List.range' 885248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1729_1_checked : (List.range' 885376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1729_2_checked : (List.range' 885504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1729_3_checked : (List.range' 885632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1729_range (index : Nat) (lower : 885248 ≤ index) (upper : index < 885760) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 885504 then
    if cut : index < 885376 then
      exact segment_sound _ 885248 128 Restriction1729_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 885376 128 Restriction1729_1_checked index (by omega) (by omega)
  else
    if cut : index < 885632 then
      exact segment_sound _ 885504 128 Restriction1729_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 885632 128 Restriction1729_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
