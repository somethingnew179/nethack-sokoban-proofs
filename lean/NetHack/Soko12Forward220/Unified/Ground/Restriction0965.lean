import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0965_0_checked : (List.range' 494080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0965_1_checked : (List.range' 494208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0965_2_checked : (List.range' 494336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0965_3_checked : (List.range' 494464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0965_range (index : Nat) (lower : 494080 ≤ index) (upper : index < 494592) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 494336 then
    if cut : index < 494208 then
      exact segment_sound _ 494080 128 Restriction0965_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 494208 128 Restriction0965_1_checked index (by omega) (by omega)
  else
    if cut : index < 494464 then
      exact segment_sound _ 494336 128 Restriction0965_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 494464 128 Restriction0965_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
