import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0148_0_checked : (List.range' 75776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0148_1_checked : (List.range' 75904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0148_2_checked : (List.range' 76032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0148_3_checked : (List.range' 76160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0148_range (index : Nat) (lower : 75776 ≤ index) (upper : index < 76288) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 76032 then
    if cut : index < 75904 then
      exact segment_sound _ 75776 128 Restriction0148_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 75904 128 Restriction0148_1_checked index (by omega) (by omega)
  else
    if cut : index < 76160 then
      exact segment_sound _ 76032 128 Restriction0148_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 76160 128 Restriction0148_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
