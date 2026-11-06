import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1597_0_checked : (List.range' 817664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1597_1_checked : (List.range' 817792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1597_2_checked : (List.range' 817920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1597_3_checked : (List.range' 818048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1597_range (index : Nat) (lower : 817664 ≤ index) (upper : index < 818176) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 817920 then
    if cut : index < 817792 then
      exact segment_sound _ 817664 128 Restriction1597_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 817792 128 Restriction1597_1_checked index (by omega) (by omega)
  else
    if cut : index < 818048 then
      exact segment_sound _ 817920 128 Restriction1597_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 818048 128 Restriction1597_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
