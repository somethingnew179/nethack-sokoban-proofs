import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1011_0_checked : (List.range' 517632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1011_1_checked : (List.range' 517760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1011_2_checked : (List.range' 517888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1011_3_checked : (List.range' 518016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1011_range (index : Nat) (lower : 517632 ≤ index) (upper : index < 518144) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 517888 then
    if cut : index < 517760 then
      exact segment_sound _ 517632 128 Restriction1011_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 517760 128 Restriction1011_1_checked index (by omega) (by omega)
  else
    if cut : index < 518016 then
      exact segment_sound _ 517888 128 Restriction1011_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 518016 128 Restriction1011_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
