import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1123_0_checked : (List.range' 574976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1123_1_checked : (List.range' 575104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1123_2_checked : (List.range' 575232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1123_3_checked : (List.range' 575360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1123_range (index : Nat) (lower : 574976 ≤ index) (upper : index < 575488) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 575232 then
    if cut : index < 575104 then
      exact segment_sound _ 574976 128 Restriction1123_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 575104 128 Restriction1123_1_checked index (by omega) (by omega)
  else
    if cut : index < 575360 then
      exact segment_sound _ 575232 128 Restriction1123_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 575360 128 Restriction1123_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
