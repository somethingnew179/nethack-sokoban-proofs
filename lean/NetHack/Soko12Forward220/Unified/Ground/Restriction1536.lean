import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1536_0_checked : (List.range' 786432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1536_1_checked : (List.range' 786560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1536_2_checked : (List.range' 786688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1536_3_checked : (List.range' 786816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1536_range (index : Nat) (lower : 786432 ≤ index) (upper : index < 786944) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 786688 then
    if cut : index < 786560 then
      exact segment_sound _ 786432 128 Restriction1536_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 786560 128 Restriction1536_1_checked index (by omega) (by omega)
  else
    if cut : index < 786816 then
      exact segment_sound _ 786688 128 Restriction1536_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 786816 128 Restriction1536_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
