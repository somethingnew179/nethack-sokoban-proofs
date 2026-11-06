import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0593_0_checked : (List.range' 303616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0593_1_checked : (List.range' 303744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0593_2_checked : (List.range' 303872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0593_3_checked : (List.range' 304000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0593_range (index : Nat) (lower : 303616 ≤ index) (upper : index < 304128) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 303872 then
    if cut : index < 303744 then
      exact segment_sound _ 303616 128 Restriction0593_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 303744 128 Restriction0593_1_checked index (by omega) (by omega)
  else
    if cut : index < 304000 then
      exact segment_sound _ 303872 128 Restriction0593_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 304000 128 Restriction0593_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
