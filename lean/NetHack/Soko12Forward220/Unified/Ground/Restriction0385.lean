import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0385_0_checked : (List.range' 197120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0385_1_checked : (List.range' 197248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0385_2_checked : (List.range' 197376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0385_3_checked : (List.range' 197504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0385_range (index : Nat) (lower : 197120 ≤ index) (upper : index < 197632) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 197376 then
    if cut : index < 197248 then
      exact segment_sound _ 197120 128 Restriction0385_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 197248 128 Restriction0385_1_checked index (by omega) (by omega)
  else
    if cut : index < 197504 then
      exact segment_sound _ 197376 128 Restriction0385_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 197504 128 Restriction0385_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
