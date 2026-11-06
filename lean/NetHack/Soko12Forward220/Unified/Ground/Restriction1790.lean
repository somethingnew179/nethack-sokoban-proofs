import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1790_0_checked : (List.range' 916480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1790_1_checked : (List.range' 916608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1790_2_checked : (List.range' 916736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1790_3_checked : (List.range' 916864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1790_range (index : Nat) (lower : 916480 ≤ index) (upper : index < 916992) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 916736 then
    if cut : index < 916608 then
      exact segment_sound _ 916480 128 Restriction1790_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 916608 128 Restriction1790_1_checked index (by omega) (by omega)
  else
    if cut : index < 916864 then
      exact segment_sound _ 916736 128 Restriction1790_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 916864 128 Restriction1790_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
