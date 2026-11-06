import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1398_0_checked : (List.range' 715776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1398_1_checked : (List.range' 715904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1398_2_checked : (List.range' 716032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1398_3_checked : (List.range' 716160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1398_range (index : Nat) (lower : 715776 ≤ index) (upper : index < 716288) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 716032 then
    if cut : index < 715904 then
      exact segment_sound _ 715776 128 Restriction1398_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 715904 128 Restriction1398_1_checked index (by omega) (by omega)
  else
    if cut : index < 716160 then
      exact segment_sound _ 716032 128 Restriction1398_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 716160 128 Restriction1398_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
