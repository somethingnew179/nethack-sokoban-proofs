import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1184_0_checked : (List.range' 606208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1184_1_checked : (List.range' 606336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1184_2_checked : (List.range' 606464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1184_3_checked : (List.range' 606592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1184_range (index : Nat) (lower : 606208 ≤ index) (upper : index < 606720) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 606464 then
    if cut : index < 606336 then
      exact segment_sound _ 606208 128 Restriction1184_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 606336 128 Restriction1184_1_checked index (by omega) (by omega)
  else
    if cut : index < 606592 then
      exact segment_sound _ 606464 128 Restriction1184_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 606592 128 Restriction1184_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
