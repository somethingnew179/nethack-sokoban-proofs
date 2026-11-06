import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1408_0_checked : (List.range' 720896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1408_1_checked : (List.range' 721024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1408_2_checked : (List.range' 721152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1408_3_checked : (List.range' 721280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1408_range (index : Nat) (lower : 720896 ≤ index) (upper : index < 721408) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 721152 then
    if cut : index < 721024 then
      exact segment_sound _ 720896 128 Restriction1408_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 721024 128 Restriction1408_1_checked index (by omega) (by omega)
  else
    if cut : index < 721280 then
      exact segment_sound _ 721152 128 Restriction1408_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 721280 128 Restriction1408_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
