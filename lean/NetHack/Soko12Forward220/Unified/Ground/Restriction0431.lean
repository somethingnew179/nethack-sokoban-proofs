import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0431_0_checked : (List.range' 220672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0431_1_checked : (List.range' 220800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0431_2_checked : (List.range' 220928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0431_3_checked : (List.range' 221056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0431_range (index : Nat) (lower : 220672 ≤ index) (upper : index < 221184) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 220928 then
    if cut : index < 220800 then
      exact segment_sound _ 220672 128 Restriction0431_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 220800 128 Restriction0431_1_checked index (by omega) (by omega)
  else
    if cut : index < 221056 then
      exact segment_sound _ 220928 128 Restriction0431_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 221056 128 Restriction0431_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
