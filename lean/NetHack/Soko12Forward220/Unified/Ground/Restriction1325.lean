import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1325_0_checked : (List.range' 678400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1325_1_checked : (List.range' 678528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1325_2_checked : (List.range' 678656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1325_3_checked : (List.range' 678784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1325_range (index : Nat) (lower : 678400 ≤ index) (upper : index < 678912) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 678656 then
    if cut : index < 678528 then
      exact segment_sound _ 678400 128 Restriction1325_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 678528 128 Restriction1325_1_checked index (by omega) (by omega)
  else
    if cut : index < 678784 then
      exact segment_sound _ 678656 128 Restriction1325_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 678784 128 Restriction1325_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
