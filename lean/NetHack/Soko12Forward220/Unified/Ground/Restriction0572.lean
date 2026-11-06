import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0572_0_checked : (List.range' 292864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0572_1_checked : (List.range' 292992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0572_2_checked : (List.range' 293120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0572_3_checked : (List.range' 293248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0572_range (index : Nat) (lower : 292864 ≤ index) (upper : index < 293376) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 293120 then
    if cut : index < 292992 then
      exact segment_sound _ 292864 128 Restriction0572_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 292992 128 Restriction0572_1_checked index (by omega) (by omega)
  else
    if cut : index < 293248 then
      exact segment_sound _ 293120 128 Restriction0572_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 293248 128 Restriction0572_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
