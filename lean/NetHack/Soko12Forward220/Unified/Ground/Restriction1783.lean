import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1783_0_checked : (List.range' 912896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1783_1_checked : (List.range' 913024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1783_2_checked : (List.range' 913152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1783_3_checked : (List.range' 913280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1783_range (index : Nat) (lower : 912896 ≤ index) (upper : index < 913408) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 913152 then
    if cut : index < 913024 then
      exact segment_sound _ 912896 128 Restriction1783_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 913024 128 Restriction1783_1_checked index (by omega) (by omega)
  else
    if cut : index < 913280 then
      exact segment_sound _ 913152 128 Restriction1783_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 913280 128 Restriction1783_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
