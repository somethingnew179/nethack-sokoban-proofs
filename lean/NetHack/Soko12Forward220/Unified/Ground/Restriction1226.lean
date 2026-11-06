import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1226_0_checked : (List.range' 627712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1226_1_checked : (List.range' 627840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1226_2_checked : (List.range' 627968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1226_3_checked : (List.range' 628096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1226_range (index : Nat) (lower : 627712 ≤ index) (upper : index < 628224) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 627968 then
    if cut : index < 627840 then
      exact segment_sound _ 627712 128 Restriction1226_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 627840 128 Restriction1226_1_checked index (by omega) (by omega)
  else
    if cut : index < 628096 then
      exact segment_sound _ 627968 128 Restriction1226_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 628096 128 Restriction1226_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
