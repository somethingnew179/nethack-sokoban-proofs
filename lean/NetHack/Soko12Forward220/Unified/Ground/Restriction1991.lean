import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1991_0_checked : (List.range' 1019392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1991_1_checked : (List.range' 1019520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1991_2_checked : (List.range' 1019648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1991_3_checked : (List.range' 1019776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1991_range (index : Nat) (lower : 1019392 ≤ index) (upper : index < 1019904) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1019648 then
    if cut : index < 1019520 then
      exact segment_sound _ 1019392 128 Restriction1991_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1019520 128 Restriction1991_1_checked index (by omega) (by omega)
  else
    if cut : index < 1019776 then
      exact segment_sound _ 1019648 128 Restriction1991_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1019776 128 Restriction1991_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
