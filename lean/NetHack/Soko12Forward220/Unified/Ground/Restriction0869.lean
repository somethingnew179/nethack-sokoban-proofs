import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0869_0_checked : (List.range' 444928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0869_1_checked : (List.range' 445056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0869_2_checked : (List.range' 445184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0869_3_checked : (List.range' 445312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0869_range (index : Nat) (lower : 444928 ≤ index) (upper : index < 445440) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 445184 then
    if cut : index < 445056 then
      exact segment_sound _ 444928 128 Restriction0869_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 445056 128 Restriction0869_1_checked index (by omega) (by omega)
  else
    if cut : index < 445312 then
      exact segment_sound _ 445184 128 Restriction0869_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 445312 128 Restriction0869_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
