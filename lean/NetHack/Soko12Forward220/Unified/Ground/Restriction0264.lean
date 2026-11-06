import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0264_0_checked : (List.range' 135168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0264_1_checked : (List.range' 135296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0264_2_checked : (List.range' 135424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0264_3_checked : (List.range' 135552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0264_range (index : Nat) (lower : 135168 ≤ index) (upper : index < 135680) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 135424 then
    if cut : index < 135296 then
      exact segment_sound _ 135168 128 Restriction0264_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 135296 128 Restriction0264_1_checked index (by omega) (by omega)
  else
    if cut : index < 135552 then
      exact segment_sound _ 135424 128 Restriction0264_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 135552 128 Restriction0264_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
