import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0453_0_checked : (List.range' 231936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0453_1_checked : (List.range' 232064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0453_2_checked : (List.range' 232192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0453_3_checked : (List.range' 232320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0453_range (index : Nat) (lower : 231936 ≤ index) (upper : index < 232448) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 232192 then
    if cut : index < 232064 then
      exact segment_sound _ 231936 128 Restriction0453_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 232064 128 Restriction0453_1_checked index (by omega) (by omega)
  else
    if cut : index < 232320 then
      exact segment_sound _ 232192 128 Restriction0453_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 232320 128 Restriction0453_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
