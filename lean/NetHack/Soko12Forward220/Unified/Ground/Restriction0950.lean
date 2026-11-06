import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0950_0_checked : (List.range' 486400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0950_1_checked : (List.range' 486528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0950_2_checked : (List.range' 486656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0950_3_checked : (List.range' 486784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0950_range (index : Nat) (lower : 486400 ≤ index) (upper : index < 486912) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 486656 then
    if cut : index < 486528 then
      exact segment_sound _ 486400 128 Restriction0950_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 486528 128 Restriction0950_1_checked index (by omega) (by omega)
  else
    if cut : index < 486784 then
      exact segment_sound _ 486656 128 Restriction0950_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 486784 128 Restriction0950_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
