import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1194_0_checked : (List.range' 611328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1194_1_checked : (List.range' 611456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1194_2_checked : (List.range' 611584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1194_3_checked : (List.range' 611712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1194_range (index : Nat) (lower : 611328 ≤ index) (upper : index < 611840) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 611584 then
    if cut : index < 611456 then
      exact segment_sound _ 611328 128 Restriction1194_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 611456 128 Restriction1194_1_checked index (by omega) (by omega)
  else
    if cut : index < 611712 then
      exact segment_sound _ 611584 128 Restriction1194_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 611712 128 Restriction1194_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
