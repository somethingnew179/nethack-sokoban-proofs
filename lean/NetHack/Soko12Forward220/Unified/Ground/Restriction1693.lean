import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1693_0_checked : (List.range' 866816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1693_1_checked : (List.range' 866944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1693_2_checked : (List.range' 867072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1693_3_checked : (List.range' 867200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1693_range (index : Nat) (lower : 866816 ≤ index) (upper : index < 867328) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 867072 then
    if cut : index < 866944 then
      exact segment_sound _ 866816 128 Restriction1693_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 866944 128 Restriction1693_1_checked index (by omega) (by omega)
  else
    if cut : index < 867200 then
      exact segment_sound _ 867072 128 Restriction1693_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 867200 128 Restriction1693_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
