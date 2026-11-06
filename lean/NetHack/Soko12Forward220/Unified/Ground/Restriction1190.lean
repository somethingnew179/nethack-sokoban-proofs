import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1190_0_checked : (List.range' 609280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1190_1_checked : (List.range' 609408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1190_2_checked : (List.range' 609536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1190_3_checked : (List.range' 609664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1190_range (index : Nat) (lower : 609280 ≤ index) (upper : index < 609792) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 609536 then
    if cut : index < 609408 then
      exact segment_sound _ 609280 128 Restriction1190_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 609408 128 Restriction1190_1_checked index (by omega) (by omega)
  else
    if cut : index < 609664 then
      exact segment_sound _ 609536 128 Restriction1190_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 609664 128 Restriction1190_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
