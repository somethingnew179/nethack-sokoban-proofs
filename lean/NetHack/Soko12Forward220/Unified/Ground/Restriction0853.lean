import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0853_0_checked : (List.range' 436736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0853_1_checked : (List.range' 436864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0853_2_checked : (List.range' 436992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0853_3_checked : (List.range' 437120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0853_range (index : Nat) (lower : 436736 ≤ index) (upper : index < 437248) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 436992 then
    if cut : index < 436864 then
      exact segment_sound _ 436736 128 Restriction0853_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 436864 128 Restriction0853_1_checked index (by omega) (by omega)
  else
    if cut : index < 437120 then
      exact segment_sound _ 436992 128 Restriction0853_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 437120 128 Restriction0853_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
