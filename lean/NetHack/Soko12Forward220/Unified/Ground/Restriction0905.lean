import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0905_0_checked : (List.range' 463360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0905_1_checked : (List.range' 463488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0905_2_checked : (List.range' 463616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0905_3_checked : (List.range' 463744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0905_range (index : Nat) (lower : 463360 ≤ index) (upper : index < 463872) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 463616 then
    if cut : index < 463488 then
      exact segment_sound _ 463360 128 Restriction0905_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 463488 128 Restriction0905_1_checked index (by omega) (by omega)
  else
    if cut : index < 463744 then
      exact segment_sound _ 463616 128 Restriction0905_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 463744 128 Restriction0905_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
