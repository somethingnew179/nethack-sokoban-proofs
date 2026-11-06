import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1566_0_checked : (List.range' 801792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1566_1_checked : (List.range' 801920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1566_2_checked : (List.range' 802048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1566_3_checked : (List.range' 802176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1566_range (index : Nat) (lower : 801792 ≤ index) (upper : index < 802304) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 802048 then
    if cut : index < 801920 then
      exact segment_sound _ 801792 128 Restriction1566_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 801920 128 Restriction1566_1_checked index (by omega) (by omega)
  else
    if cut : index < 802176 then
      exact segment_sound _ 802048 128 Restriction1566_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 802176 128 Restriction1566_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
