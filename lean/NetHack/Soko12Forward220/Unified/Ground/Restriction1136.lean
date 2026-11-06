import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1136_0_checked : (List.range' 581632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1136_1_checked : (List.range' 581760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1136_2_checked : (List.range' 581888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1136_3_checked : (List.range' 582016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1136_range (index : Nat) (lower : 581632 ≤ index) (upper : index < 582144) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 581888 then
    if cut : index < 581760 then
      exact segment_sound _ 581632 128 Restriction1136_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 581760 128 Restriction1136_1_checked index (by omega) (by omega)
  else
    if cut : index < 582016 then
      exact segment_sound _ 581888 128 Restriction1136_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 582016 128 Restriction1136_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
