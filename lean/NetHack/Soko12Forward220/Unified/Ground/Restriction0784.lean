import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0784_0_checked : (List.range' 401408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0784_1_checked : (List.range' 401536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0784_2_checked : (List.range' 401664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0784_3_checked : (List.range' 401792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0784_range (index : Nat) (lower : 401408 ≤ index) (upper : index < 401920) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 401664 then
    if cut : index < 401536 then
      exact segment_sound _ 401408 128 Restriction0784_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 401536 128 Restriction0784_1_checked index (by omega) (by omega)
  else
    if cut : index < 401792 then
      exact segment_sound _ 401664 128 Restriction0784_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 401792 128 Restriction0784_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
