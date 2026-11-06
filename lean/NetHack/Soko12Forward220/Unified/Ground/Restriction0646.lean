import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0646_0_checked : (List.range' 330752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0646_1_checked : (List.range' 330880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0646_2_checked : (List.range' 331008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0646_3_checked : (List.range' 331136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0646_range (index : Nat) (lower : 330752 ≤ index) (upper : index < 331264) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 331008 then
    if cut : index < 330880 then
      exact segment_sound _ 330752 128 Restriction0646_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 330880 128 Restriction0646_1_checked index (by omega) (by omega)
  else
    if cut : index < 331136 then
      exact segment_sound _ 331008 128 Restriction0646_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 331136 128 Restriction0646_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
