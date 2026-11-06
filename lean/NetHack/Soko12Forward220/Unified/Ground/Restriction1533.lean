import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1533_0_checked : (List.range' 784896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1533_1_checked : (List.range' 785024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1533_2_checked : (List.range' 785152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1533_3_checked : (List.range' 785280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1533_range (index : Nat) (lower : 784896 ≤ index) (upper : index < 785408) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 785152 then
    if cut : index < 785024 then
      exact segment_sound _ 784896 128 Restriction1533_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 785024 128 Restriction1533_1_checked index (by omega) (by omega)
  else
    if cut : index < 785280 then
      exact segment_sound _ 785152 128 Restriction1533_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 785280 128 Restriction1533_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
