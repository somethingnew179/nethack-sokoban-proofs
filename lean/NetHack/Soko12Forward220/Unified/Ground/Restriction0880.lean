import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0880_0_checked : (List.range' 450560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0880_1_checked : (List.range' 450688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0880_2_checked : (List.range' 450816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0880_3_checked : (List.range' 450944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0880_range (index : Nat) (lower : 450560 ≤ index) (upper : index < 451072) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 450816 then
    if cut : index < 450688 then
      exact segment_sound _ 450560 128 Restriction0880_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 450688 128 Restriction0880_1_checked index (by omega) (by omega)
  else
    if cut : index < 450944 then
      exact segment_sound _ 450816 128 Restriction0880_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 450944 128 Restriction0880_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
