import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1697_0_checked : (List.range' 868864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1697_1_checked : (List.range' 868992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1697_2_checked : (List.range' 869120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1697_3_checked : (List.range' 869248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1697_range (index : Nat) (lower : 868864 ≤ index) (upper : index < 869376) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 869120 then
    if cut : index < 868992 then
      exact segment_sound _ 868864 128 Restriction1697_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 868992 128 Restriction1697_1_checked index (by omega) (by omega)
  else
    if cut : index < 869248 then
      exact segment_sound _ 869120 128 Restriction1697_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 869248 128 Restriction1697_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
