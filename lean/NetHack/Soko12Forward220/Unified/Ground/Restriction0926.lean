import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0926_0_checked : (List.range' 474112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0926_1_checked : (List.range' 474240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0926_2_checked : (List.range' 474368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0926_3_checked : (List.range' 474496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0926_range (index : Nat) (lower : 474112 ≤ index) (upper : index < 474624) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 474368 then
    if cut : index < 474240 then
      exact segment_sound _ 474112 128 Restriction0926_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 474240 128 Restriction0926_1_checked index (by omega) (by omega)
  else
    if cut : index < 474496 then
      exact segment_sound _ 474368 128 Restriction0926_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 474496 128 Restriction0926_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
