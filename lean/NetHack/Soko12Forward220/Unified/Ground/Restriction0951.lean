import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0951_0_checked : (List.range' 486912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0951_1_checked : (List.range' 487040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0951_2_checked : (List.range' 487168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0951_3_checked : (List.range' 487296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0951_range (index : Nat) (lower : 486912 ≤ index) (upper : index < 487424) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 487168 then
    if cut : index < 487040 then
      exact segment_sound _ 486912 128 Restriction0951_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 487040 128 Restriction0951_1_checked index (by omega) (by omega)
  else
    if cut : index < 487296 then
      exact segment_sound _ 487168 128 Restriction0951_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 487296 128 Restriction0951_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
