import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1496_0_checked : (List.range' 765952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1496_1_checked : (List.range' 766080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1496_2_checked : (List.range' 766208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1496_3_checked : (List.range' 766336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1496_range (index : Nat) (lower : 765952 ≤ index) (upper : index < 766464) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 766208 then
    if cut : index < 766080 then
      exact segment_sound _ 765952 128 Restriction1496_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 766080 128 Restriction1496_1_checked index (by omega) (by omega)
  else
    if cut : index < 766336 then
      exact segment_sound _ 766208 128 Restriction1496_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 766336 128 Restriction1496_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
