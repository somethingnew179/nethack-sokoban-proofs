import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0855_0_checked : (List.range' 437760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0855_1_checked : (List.range' 437888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0855_2_checked : (List.range' 438016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0855_3_checked : (List.range' 438144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0855_range (index : Nat) (lower : 437760 ≤ index) (upper : index < 438272) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 438016 then
    if cut : index < 437888 then
      exact segment_sound _ 437760 128 Restriction0855_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 437888 128 Restriction0855_1_checked index (by omega) (by omega)
  else
    if cut : index < 438144 then
      exact segment_sound _ 438016 128 Restriction0855_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 438144 128 Restriction0855_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
