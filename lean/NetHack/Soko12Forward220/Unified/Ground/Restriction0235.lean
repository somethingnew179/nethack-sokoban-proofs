import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0235_0_checked : (List.range' 120320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0235_1_checked : (List.range' 120448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0235_2_checked : (List.range' 120576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0235_3_checked : (List.range' 120704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0235_range (index : Nat) (lower : 120320 ≤ index) (upper : index < 120832) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 120576 then
    if cut : index < 120448 then
      exact segment_sound _ 120320 128 Restriction0235_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 120448 128 Restriction0235_1_checked index (by omega) (by omega)
  else
    if cut : index < 120704 then
      exact segment_sound _ 120576 128 Restriction0235_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 120704 128 Restriction0235_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
