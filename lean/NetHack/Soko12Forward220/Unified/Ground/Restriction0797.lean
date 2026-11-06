import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0797_0_checked : (List.range' 408064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0797_1_checked : (List.range' 408192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0797_2_checked : (List.range' 408320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0797_3_checked : (List.range' 408448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0797_range (index : Nat) (lower : 408064 ≤ index) (upper : index < 408576) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 408320 then
    if cut : index < 408192 then
      exact segment_sound _ 408064 128 Restriction0797_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 408192 128 Restriction0797_1_checked index (by omega) (by omega)
  else
    if cut : index < 408448 then
      exact segment_sound _ 408320 128 Restriction0797_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 408448 128 Restriction0797_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
