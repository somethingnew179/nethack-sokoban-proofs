import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1993_0_checked : (List.range' 1020416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1993_1_checked : (List.range' 1020544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1993_2_checked : (List.range' 1020672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1993_3_checked : (List.range' 1020800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1993_range (index : Nat) (lower : 1020416 ≤ index) (upper : index < 1020928) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1020672 then
    if cut : index < 1020544 then
      exact segment_sound _ 1020416 128 Restriction1993_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1020544 128 Restriction1993_1_checked index (by omega) (by omega)
  else
    if cut : index < 1020800 then
      exact segment_sound _ 1020672 128 Restriction1993_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1020800 128 Restriction1993_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
