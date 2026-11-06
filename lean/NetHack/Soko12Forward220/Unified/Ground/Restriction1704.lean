import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1704_0_checked : (List.range' 872448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1704_1_checked : (List.range' 872576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1704_2_checked : (List.range' 872704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1704_3_checked : (List.range' 872832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1704_range (index : Nat) (lower : 872448 ≤ index) (upper : index < 872960) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 872704 then
    if cut : index < 872576 then
      exact segment_sound _ 872448 128 Restriction1704_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 872576 128 Restriction1704_1_checked index (by omega) (by omega)
  else
    if cut : index < 872832 then
      exact segment_sound _ 872704 128 Restriction1704_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 872832 128 Restriction1704_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
