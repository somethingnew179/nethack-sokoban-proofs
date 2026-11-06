import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1103_0_checked : (List.range' 564736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1103_1_checked : (List.range' 564864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1103_2_checked : (List.range' 564992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1103_3_checked : (List.range' 565120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1103_range (index : Nat) (lower : 564736 ≤ index) (upper : index < 565248) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 564992 then
    if cut : index < 564864 then
      exact segment_sound _ 564736 128 Restriction1103_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 564864 128 Restriction1103_1_checked index (by omega) (by omega)
  else
    if cut : index < 565120 then
      exact segment_sound _ 564992 128 Restriction1103_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 565120 128 Restriction1103_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
