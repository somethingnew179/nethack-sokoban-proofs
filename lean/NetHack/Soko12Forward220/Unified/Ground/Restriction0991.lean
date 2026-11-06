import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0991_0_checked : (List.range' 507392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0991_1_checked : (List.range' 507520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0991_2_checked : (List.range' 507648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0991_3_checked : (List.range' 507776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0991_range (index : Nat) (lower : 507392 ≤ index) (upper : index < 507904) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 507648 then
    if cut : index < 507520 then
      exact segment_sound _ 507392 128 Restriction0991_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 507520 128 Restriction0991_1_checked index (by omega) (by omega)
  else
    if cut : index < 507776 then
      exact segment_sound _ 507648 128 Restriction0991_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 507776 128 Restriction0991_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
