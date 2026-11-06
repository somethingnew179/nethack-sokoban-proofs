import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1652_0_checked : (List.range' 845824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1652_1_checked : (List.range' 845952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1652_2_checked : (List.range' 846080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1652_3_checked : (List.range' 846208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1652_range (index : Nat) (lower : 845824 ≤ index) (upper : index < 846336) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 846080 then
    if cut : index < 845952 then
      exact segment_sound _ 845824 128 Restriction1652_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 845952 128 Restriction1652_1_checked index (by omega) (by omega)
  else
    if cut : index < 846208 then
      exact segment_sound _ 846080 128 Restriction1652_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 846208 128 Restriction1652_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
