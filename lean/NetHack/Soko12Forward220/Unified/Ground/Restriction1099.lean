import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1099_0_checked : (List.range' 562688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1099_1_checked : (List.range' 562816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1099_2_checked : (List.range' 562944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1099_3_checked : (List.range' 563072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1099_range (index : Nat) (lower : 562688 ≤ index) (upper : index < 563200) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 562944 then
    if cut : index < 562816 then
      exact segment_sound _ 562688 128 Restriction1099_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 562816 128 Restriction1099_1_checked index (by omega) (by omega)
  else
    if cut : index < 563072 then
      exact segment_sound _ 562944 128 Restriction1099_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 563072 128 Restriction1099_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
