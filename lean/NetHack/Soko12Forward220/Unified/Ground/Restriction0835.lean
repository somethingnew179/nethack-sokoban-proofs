import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0835_0_checked : (List.range' 427520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0835_1_checked : (List.range' 427648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0835_2_checked : (List.range' 427776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0835_3_checked : (List.range' 427904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0835_range (index : Nat) (lower : 427520 ≤ index) (upper : index < 428032) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 427776 then
    if cut : index < 427648 then
      exact segment_sound _ 427520 128 Restriction0835_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 427648 128 Restriction0835_1_checked index (by omega) (by omega)
  else
    if cut : index < 427904 then
      exact segment_sound _ 427776 128 Restriction0835_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 427904 128 Restriction0835_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
