import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0052_0_checked : (List.range' 26624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0052_1_checked : (List.range' 26752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0052_2_checked : (List.range' 26880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0052_3_checked : (List.range' 27008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0052_range (index : Nat) (lower : 26624 ≤ index) (upper : index < 27136) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 26880 then
    if cut : index < 26752 then
      exact segment_sound _ 26624 128 Restriction0052_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 26752 128 Restriction0052_1_checked index (by omega) (by omega)
  else
    if cut : index < 27008 then
      exact segment_sound _ 26880 128 Restriction0052_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 27008 128 Restriction0052_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
