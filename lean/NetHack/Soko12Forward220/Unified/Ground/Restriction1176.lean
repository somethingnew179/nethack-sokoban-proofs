import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1176_0_checked : (List.range' 602112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1176_1_checked : (List.range' 602240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1176_2_checked : (List.range' 602368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1176_3_checked : (List.range' 602496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1176_range (index : Nat) (lower : 602112 ≤ index) (upper : index < 602624) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 602368 then
    if cut : index < 602240 then
      exact segment_sound _ 602112 128 Restriction1176_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 602240 128 Restriction1176_1_checked index (by omega) (by omega)
  else
    if cut : index < 602496 then
      exact segment_sound _ 602368 128 Restriction1176_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 602496 128 Restriction1176_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
