import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0334_0_checked : (List.range' 171008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0334_1_checked : (List.range' 171136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0334_2_checked : (List.range' 171264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0334_3_checked : (List.range' 171392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0334_range (index : Nat) (lower : 171008 ≤ index) (upper : index < 171520) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 171264 then
    if cut : index < 171136 then
      exact segment_sound _ 171008 128 Restriction0334_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 171136 128 Restriction0334_1_checked index (by omega) (by omega)
  else
    if cut : index < 171392 then
      exact segment_sound _ 171264 128 Restriction0334_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 171392 128 Restriction0334_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
