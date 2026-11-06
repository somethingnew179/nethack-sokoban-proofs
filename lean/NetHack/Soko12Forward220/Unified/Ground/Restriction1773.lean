import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1773_0_checked : (List.range' 907776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1773_1_checked : (List.range' 907904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1773_2_checked : (List.range' 908032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1773_3_checked : (List.range' 908160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1773_range (index : Nat) (lower : 907776 ≤ index) (upper : index < 908288) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 908032 then
    if cut : index < 907904 then
      exact segment_sound _ 907776 128 Restriction1773_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 907904 128 Restriction1773_1_checked index (by omega) (by omega)
  else
    if cut : index < 908160 then
      exact segment_sound _ 908032 128 Restriction1773_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 908160 128 Restriction1773_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
