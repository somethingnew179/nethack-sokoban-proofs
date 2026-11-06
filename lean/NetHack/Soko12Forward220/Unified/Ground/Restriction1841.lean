import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1841_0_checked : (List.range' 942592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1841_1_checked : (List.range' 942720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1841_2_checked : (List.range' 942848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1841_3_checked : (List.range' 942976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1841_range (index : Nat) (lower : 942592 ≤ index) (upper : index < 943104) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 942848 then
    if cut : index < 942720 then
      exact segment_sound _ 942592 128 Restriction1841_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 942720 128 Restriction1841_1_checked index (by omega) (by omega)
  else
    if cut : index < 942976 then
      exact segment_sound _ 942848 128 Restriction1841_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 942976 128 Restriction1841_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
