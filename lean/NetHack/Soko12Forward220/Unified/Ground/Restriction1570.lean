import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1570_0_checked : (List.range' 803840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1570_1_checked : (List.range' 803968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1570_2_checked : (List.range' 804096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1570_3_checked : (List.range' 804224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1570_range (index : Nat) (lower : 803840 ≤ index) (upper : index < 804352) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 804096 then
    if cut : index < 803968 then
      exact segment_sound _ 803840 128 Restriction1570_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 803968 128 Restriction1570_1_checked index (by omega) (by omega)
  else
    if cut : index < 804224 then
      exact segment_sound _ 804096 128 Restriction1570_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 804224 128 Restriction1570_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
