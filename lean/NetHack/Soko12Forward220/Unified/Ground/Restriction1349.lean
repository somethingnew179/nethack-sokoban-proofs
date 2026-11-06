import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1349_0_checked : (List.range' 690688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1349_1_checked : (List.range' 690816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1349_2_checked : (List.range' 690944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1349_3_checked : (List.range' 691072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1349_range (index : Nat) (lower : 690688 ≤ index) (upper : index < 691200) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 690944 then
    if cut : index < 690816 then
      exact segment_sound _ 690688 128 Restriction1349_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 690816 128 Restriction1349_1_checked index (by omega) (by omega)
  else
    if cut : index < 691072 then
      exact segment_sound _ 690944 128 Restriction1349_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 691072 128 Restriction1349_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
