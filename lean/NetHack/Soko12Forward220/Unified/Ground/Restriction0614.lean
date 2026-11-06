import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0614_0_checked : (List.range' 314368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0614_1_checked : (List.range' 314496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0614_2_checked : (List.range' 314624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0614_3_checked : (List.range' 314752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0614_range (index : Nat) (lower : 314368 ≤ index) (upper : index < 314880) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 314624 then
    if cut : index < 314496 then
      exact segment_sound _ 314368 128 Restriction0614_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 314496 128 Restriction0614_1_checked index (by omega) (by omega)
  else
    if cut : index < 314752 then
      exact segment_sound _ 314624 128 Restriction0614_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 314752 128 Restriction0614_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
