import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0681_0_checked : (List.range' 348672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0681_1_checked : (List.range' 348800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0681_2_checked : (List.range' 348928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0681_3_checked : (List.range' 349056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0681_range (index : Nat) (lower : 348672 ≤ index) (upper : index < 349184) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 348928 then
    if cut : index < 348800 then
      exact segment_sound _ 348672 128 Restriction0681_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 348800 128 Restriction0681_1_checked index (by omega) (by omega)
  else
    if cut : index < 349056 then
      exact segment_sound _ 348928 128 Restriction0681_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 349056 128 Restriction0681_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
