import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1429_0_checked : (List.range' 731648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1429_1_checked : (List.range' 731776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1429_2_checked : (List.range' 731904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1429_3_checked : (List.range' 732032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1429_range (index : Nat) (lower : 731648 ≤ index) (upper : index < 732160) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 731904 then
    if cut : index < 731776 then
      exact segment_sound _ 731648 128 Restriction1429_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 731776 128 Restriction1429_1_checked index (by omega) (by omega)
  else
    if cut : index < 732032 then
      exact segment_sound _ 731904 128 Restriction1429_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 732032 128 Restriction1429_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
