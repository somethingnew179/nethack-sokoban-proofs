import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1976_0_checked : (List.range' 1011712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1976_1_checked : (List.range' 1011840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1976_2_checked : (List.range' 1011968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1976_3_checked : (List.range' 1012096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1976_range (index : Nat) (lower : 1011712 ≤ index) (upper : index < 1012224) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1011968 then
    if cut : index < 1011840 then
      exact segment_sound _ 1011712 128 Restriction1976_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1011840 128 Restriction1976_1_checked index (by omega) (by omega)
  else
    if cut : index < 1012096 then
      exact segment_sound _ 1011968 128 Restriction1976_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1012096 128 Restriction1976_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
