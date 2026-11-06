import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0979_0_checked : (List.range' 501248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0979_1_checked : (List.range' 501376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0979_2_checked : (List.range' 501504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0979_3_checked : (List.range' 501632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0979_range (index : Nat) (lower : 501248 ≤ index) (upper : index < 501760) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 501504 then
    if cut : index < 501376 then
      exact segment_sound _ 501248 128 Restriction0979_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 501376 128 Restriction0979_1_checked index (by omega) (by omega)
  else
    if cut : index < 501632 then
      exact segment_sound _ 501504 128 Restriction0979_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 501632 128 Restriction0979_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
