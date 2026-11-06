import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1872_0_checked : (List.range' 958464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1872_1_checked : (List.range' 958592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1872_2_checked : (List.range' 958720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1872_3_checked : (List.range' 958848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1872_range (index : Nat) (lower : 958464 ≤ index) (upper : index < 958976) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 958720 then
    if cut : index < 958592 then
      exact segment_sound _ 958464 128 Restriction1872_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 958592 128 Restriction1872_1_checked index (by omega) (by omega)
  else
    if cut : index < 958848 then
      exact segment_sound _ 958720 128 Restriction1872_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 958848 128 Restriction1872_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
