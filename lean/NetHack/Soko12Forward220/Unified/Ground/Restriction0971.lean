import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0971_0_checked : (List.range' 497152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0971_1_checked : (List.range' 497280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0971_2_checked : (List.range' 497408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0971_3_checked : (List.range' 497536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0971_range (index : Nat) (lower : 497152 ≤ index) (upper : index < 497664) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 497408 then
    if cut : index < 497280 then
      exact segment_sound _ 497152 128 Restriction0971_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 497280 128 Restriction0971_1_checked index (by omega) (by omega)
  else
    if cut : index < 497536 then
      exact segment_sound _ 497408 128 Restriction0971_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 497536 128 Restriction0971_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
