import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0022_0_checked : (List.range' 11264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0022_1_checked : (List.range' 11392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0022_2_checked : (List.range' 11520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0022_3_checked : (List.range' 11648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0022_range (index : Nat) (lower : 11264 ≤ index) (upper : index < 11776) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 11520 then
    if cut : index < 11392 then
      exact segment_sound _ 11264 128 Restriction0022_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 11392 128 Restriction0022_1_checked index (by omega) (by omega)
  else
    if cut : index < 11648 then
      exact segment_sound _ 11520 128 Restriction0022_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 11648 128 Restriction0022_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
