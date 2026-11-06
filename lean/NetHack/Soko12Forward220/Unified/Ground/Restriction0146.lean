import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0146_0_checked : (List.range' 74752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0146_1_checked : (List.range' 74880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0146_2_checked : (List.range' 75008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0146_3_checked : (List.range' 75136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0146_range (index : Nat) (lower : 74752 ≤ index) (upper : index < 75264) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 75008 then
    if cut : index < 74880 then
      exact segment_sound _ 74752 128 Restriction0146_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 74880 128 Restriction0146_1_checked index (by omega) (by omega)
  else
    if cut : index < 75136 then
      exact segment_sound _ 75008 128 Restriction0146_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 75136 128 Restriction0146_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
