import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0273_0_checked : (List.range' 139776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0273_1_checked : (List.range' 139904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0273_2_checked : (List.range' 140032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0273_3_checked : (List.range' 140160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0273_range (index : Nat) (lower : 139776 ≤ index) (upper : index < 140288) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 140032 then
    if cut : index < 139904 then
      exact segment_sound _ 139776 128 Restriction0273_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 139904 128 Restriction0273_1_checked index (by omega) (by omega)
  else
    if cut : index < 140160 then
      exact segment_sound _ 140032 128 Restriction0273_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 140160 128 Restriction0273_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
