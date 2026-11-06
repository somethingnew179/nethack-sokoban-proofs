import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0543_0_checked : (List.range' 278016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0543_1_checked : (List.range' 278144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0543_2_checked : (List.range' 278272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0543_3_checked : (List.range' 278400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0543_range (index : Nat) (lower : 278016 ≤ index) (upper : index < 278528) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 278272 then
    if cut : index < 278144 then
      exact segment_sound _ 278016 128 Restriction0543_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 278144 128 Restriction0543_1_checked index (by omega) (by omega)
  else
    if cut : index < 278400 then
      exact segment_sound _ 278272 128 Restriction0543_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 278400 128 Restriction0543_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
