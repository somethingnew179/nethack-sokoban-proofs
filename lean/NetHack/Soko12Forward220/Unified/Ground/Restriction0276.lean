import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0276_0_checked : (List.range' 141312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0276_1_checked : (List.range' 141440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0276_2_checked : (List.range' 141568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0276_3_checked : (List.range' 141696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0276_range (index : Nat) (lower : 141312 ≤ index) (upper : index < 141824) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 141568 then
    if cut : index < 141440 then
      exact segment_sound _ 141312 128 Restriction0276_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 141440 128 Restriction0276_1_checked index (by omega) (by omega)
  else
    if cut : index < 141696 then
      exact segment_sound _ 141568 128 Restriction0276_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 141696 128 Restriction0276_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
