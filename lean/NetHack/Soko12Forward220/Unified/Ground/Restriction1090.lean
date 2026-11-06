import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1090_0_checked : (List.range' 558080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1090_1_checked : (List.range' 558208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1090_2_checked : (List.range' 558336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1090_3_checked : (List.range' 558464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1090_range (index : Nat) (lower : 558080 ≤ index) (upper : index < 558592) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 558336 then
    if cut : index < 558208 then
      exact segment_sound _ 558080 128 Restriction1090_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 558208 128 Restriction1090_1_checked index (by omega) (by omega)
  else
    if cut : index < 558464 then
      exact segment_sound _ 558336 128 Restriction1090_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 558464 128 Restriction1090_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
