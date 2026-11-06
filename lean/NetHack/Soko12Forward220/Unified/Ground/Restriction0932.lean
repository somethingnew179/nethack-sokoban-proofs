import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0932_0_checked : (List.range' 477184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0932_1_checked : (List.range' 477312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0932_2_checked : (List.range' 477440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0932_3_checked : (List.range' 477568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0932_range (index : Nat) (lower : 477184 ≤ index) (upper : index < 477696) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 477440 then
    if cut : index < 477312 then
      exact segment_sound _ 477184 128 Restriction0932_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 477312 128 Restriction0932_1_checked index (by omega) (by omega)
  else
    if cut : index < 477568 then
      exact segment_sound _ 477440 128 Restriction0932_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 477568 128 Restriction0932_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
