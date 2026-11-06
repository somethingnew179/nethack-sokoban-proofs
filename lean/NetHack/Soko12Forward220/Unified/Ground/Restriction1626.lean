import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1626_0_checked : (List.range' 832512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1626_1_checked : (List.range' 832640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1626_2_checked : (List.range' 832768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1626_3_checked : (List.range' 832896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1626_range (index : Nat) (lower : 832512 ≤ index) (upper : index < 833024) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 832768 then
    if cut : index < 832640 then
      exact segment_sound _ 832512 128 Restriction1626_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 832640 128 Restriction1626_1_checked index (by omega) (by omega)
  else
    if cut : index < 832896 then
      exact segment_sound _ 832768 128 Restriction1626_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 832896 128 Restriction1626_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
