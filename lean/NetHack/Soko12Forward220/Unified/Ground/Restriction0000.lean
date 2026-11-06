import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0000_0_checked : (List.range' 0 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0000_1_checked : (List.range' 128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0000_2_checked : (List.range' 256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0000_3_checked : (List.range' 384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0000_range (index : Nat) (lower : 0 ≤ index) (upper : index < 512) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 256 then
    if cut : index < 128 then
      exact segment_sound _ 0 128 Restriction0000_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 128 128 Restriction0000_1_checked index (by omega) (by omega)
  else
    if cut : index < 384 then
      exact segment_sound _ 256 128 Restriction0000_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 384 128 Restriction0000_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
