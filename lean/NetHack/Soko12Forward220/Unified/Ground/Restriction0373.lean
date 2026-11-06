import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0373_0_checked : (List.range' 190976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0373_1_checked : (List.range' 191104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0373_2_checked : (List.range' 191232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0373_3_checked : (List.range' 191360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0373_range (index : Nat) (lower : 190976 ≤ index) (upper : index < 191488) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 191232 then
    if cut : index < 191104 then
      exact segment_sound _ 190976 128 Restriction0373_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 191104 128 Restriction0373_1_checked index (by omega) (by omega)
  else
    if cut : index < 191360 then
      exact segment_sound _ 191232 128 Restriction0373_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 191360 128 Restriction0373_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
