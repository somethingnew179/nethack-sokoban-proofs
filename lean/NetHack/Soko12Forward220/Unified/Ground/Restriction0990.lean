import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0990_0_checked : (List.range' 506880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0990_1_checked : (List.range' 507008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0990_2_checked : (List.range' 507136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0990_3_checked : (List.range' 507264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0990_range (index : Nat) (lower : 506880 ≤ index) (upper : index < 507392) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 507136 then
    if cut : index < 507008 then
      exact segment_sound _ 506880 128 Restriction0990_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 507008 128 Restriction0990_1_checked index (by omega) (by omega)
  else
    if cut : index < 507264 then
      exact segment_sound _ 507136 128 Restriction0990_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 507264 128 Restriction0990_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
