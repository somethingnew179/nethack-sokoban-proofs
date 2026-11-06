import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0908_0_checked : (List.range' 464896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0908_1_checked : (List.range' 465024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0908_2_checked : (List.range' 465152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0908_3_checked : (List.range' 465280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0908_range (index : Nat) (lower : 464896 ≤ index) (upper : index < 465408) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 465152 then
    if cut : index < 465024 then
      exact segment_sound _ 464896 128 Restriction0908_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 465024 128 Restriction0908_1_checked index (by omega) (by omega)
  else
    if cut : index < 465280 then
      exact segment_sound _ 465152 128 Restriction0908_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 465280 128 Restriction0908_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
