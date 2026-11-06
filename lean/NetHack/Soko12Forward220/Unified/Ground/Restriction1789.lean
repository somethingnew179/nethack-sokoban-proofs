import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1789_0_checked : (List.range' 915968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1789_1_checked : (List.range' 916096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1789_2_checked : (List.range' 916224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1789_3_checked : (List.range' 916352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1789_range (index : Nat) (lower : 915968 ≤ index) (upper : index < 916480) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 916224 then
    if cut : index < 916096 then
      exact segment_sound _ 915968 128 Restriction1789_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 916096 128 Restriction1789_1_checked index (by omega) (by omega)
  else
    if cut : index < 916352 then
      exact segment_sound _ 916224 128 Restriction1789_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 916352 128 Restriction1789_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
