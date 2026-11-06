import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0845_0_checked : (List.range' 432640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0845_1_checked : (List.range' 432768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0845_2_checked : (List.range' 432896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0845_3_checked : (List.range' 433024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0845_range (index : Nat) (lower : 432640 ≤ index) (upper : index < 433152) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 432896 then
    if cut : index < 432768 then
      exact segment_sound _ 432640 128 Restriction0845_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 432768 128 Restriction0845_1_checked index (by omega) (by omega)
  else
    if cut : index < 433024 then
      exact segment_sound _ 432896 128 Restriction0845_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 433024 128 Restriction0845_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
