import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1305_0_checked : (List.range' 668160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1305_1_checked : (List.range' 668288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1305_2_checked : (List.range' 668416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1305_3_checked : (List.range' 668544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1305_range (index : Nat) (lower : 668160 ≤ index) (upper : index < 668672) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 668416 then
    if cut : index < 668288 then
      exact segment_sound _ 668160 128 Restriction1305_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 668288 128 Restriction1305_1_checked index (by omega) (by omega)
  else
    if cut : index < 668544 then
      exact segment_sound _ 668416 128 Restriction1305_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 668544 128 Restriction1305_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
