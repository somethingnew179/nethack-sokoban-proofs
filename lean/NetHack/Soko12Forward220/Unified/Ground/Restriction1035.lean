import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1035_0_checked : (List.range' 529920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1035_1_checked : (List.range' 530048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1035_2_checked : (List.range' 530176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1035_3_checked : (List.range' 530304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1035_range (index : Nat) (lower : 529920 ≤ index) (upper : index < 530432) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 530176 then
    if cut : index < 530048 then
      exact segment_sound _ 529920 128 Restriction1035_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 530048 128 Restriction1035_1_checked index (by omega) (by omega)
  else
    if cut : index < 530304 then
      exact segment_sound _ 530176 128 Restriction1035_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 530304 128 Restriction1035_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
