import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0333_0_checked : (List.range' 170496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0333_1_checked : (List.range' 170624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0333_2_checked : (List.range' 170752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0333_3_checked : (List.range' 170880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0333_range (index : Nat) (lower : 170496 ≤ index) (upper : index < 171008) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 170752 then
    if cut : index < 170624 then
      exact segment_sound _ 170496 128 Restriction0333_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 170624 128 Restriction0333_1_checked index (by omega) (by omega)
  else
    if cut : index < 170880 then
      exact segment_sound _ 170752 128 Restriction0333_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 170880 128 Restriction0333_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
