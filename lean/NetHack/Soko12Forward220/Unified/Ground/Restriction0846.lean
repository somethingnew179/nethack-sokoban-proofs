import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0846_0_checked : (List.range' 433152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0846_1_checked : (List.range' 433280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0846_2_checked : (List.range' 433408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0846_3_checked : (List.range' 433536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0846_range (index : Nat) (lower : 433152 ≤ index) (upper : index < 433664) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 433408 then
    if cut : index < 433280 then
      exact segment_sound _ 433152 128 Restriction0846_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 433280 128 Restriction0846_1_checked index (by omega) (by omega)
  else
    if cut : index < 433536 then
      exact segment_sound _ 433408 128 Restriction0846_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 433536 128 Restriction0846_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
