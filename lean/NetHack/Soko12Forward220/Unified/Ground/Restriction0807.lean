import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0807_0_checked : (List.range' 413184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0807_1_checked : (List.range' 413312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0807_2_checked : (List.range' 413440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0807_3_checked : (List.range' 413568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0807_range (index : Nat) (lower : 413184 ≤ index) (upper : index < 413696) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 413440 then
    if cut : index < 413312 then
      exact segment_sound _ 413184 128 Restriction0807_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 413312 128 Restriction0807_1_checked index (by omega) (by omega)
  else
    if cut : index < 413568 then
      exact segment_sound _ 413440 128 Restriction0807_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 413568 128 Restriction0807_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
