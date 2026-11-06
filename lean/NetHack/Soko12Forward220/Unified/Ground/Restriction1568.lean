import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1568_0_checked : (List.range' 802816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1568_1_checked : (List.range' 802944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1568_2_checked : (List.range' 803072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1568_3_checked : (List.range' 803200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1568_range (index : Nat) (lower : 802816 ≤ index) (upper : index < 803328) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 803072 then
    if cut : index < 802944 then
      exact segment_sound _ 802816 128 Restriction1568_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 802944 128 Restriction1568_1_checked index (by omega) (by omega)
  else
    if cut : index < 803200 then
      exact segment_sound _ 803072 128 Restriction1568_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 803200 128 Restriction1568_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
