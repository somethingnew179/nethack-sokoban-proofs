import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1264_0_checked : (List.range' 647168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1264_1_checked : (List.range' 647296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1264_2_checked : (List.range' 647424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1264_3_checked : (List.range' 647552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1264_range (index : Nat) (lower : 647168 ≤ index) (upper : index < 647680) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 647424 then
    if cut : index < 647296 then
      exact segment_sound _ 647168 128 Restriction1264_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 647296 128 Restriction1264_1_checked index (by omega) (by omega)
  else
    if cut : index < 647552 then
      exact segment_sound _ 647424 128 Restriction1264_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 647552 128 Restriction1264_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
