import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0859_0_checked : (List.range' 439808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0859_1_checked : (List.range' 439936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0859_2_checked : (List.range' 440064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0859_3_checked : (List.range' 440192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0859_range (index : Nat) (lower : 439808 ≤ index) (upper : index < 440320) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 440064 then
    if cut : index < 439936 then
      exact segment_sound _ 439808 128 Restriction0859_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 439936 128 Restriction0859_1_checked index (by omega) (by omega)
  else
    if cut : index < 440192 then
      exact segment_sound _ 440064 128 Restriction0859_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 440192 128 Restriction0859_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
