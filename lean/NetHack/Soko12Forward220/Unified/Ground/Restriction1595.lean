import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1595_0_checked : (List.range' 816640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1595_1_checked : (List.range' 816768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1595_2_checked : (List.range' 816896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1595_3_checked : (List.range' 817024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1595_range (index : Nat) (lower : 816640 ≤ index) (upper : index < 817152) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 816896 then
    if cut : index < 816768 then
      exact segment_sound _ 816640 128 Restriction1595_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 816768 128 Restriction1595_1_checked index (by omega) (by omega)
  else
    if cut : index < 817024 then
      exact segment_sound _ 816896 128 Restriction1595_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 817024 128 Restriction1595_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
