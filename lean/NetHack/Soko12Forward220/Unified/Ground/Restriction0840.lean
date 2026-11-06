import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0840_0_checked : (List.range' 430080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0840_1_checked : (List.range' 430208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0840_2_checked : (List.range' 430336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0840_3_checked : (List.range' 430464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0840_range (index : Nat) (lower : 430080 ≤ index) (upper : index < 430592) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 430336 then
    if cut : index < 430208 then
      exact segment_sound _ 430080 128 Restriction0840_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 430208 128 Restriction0840_1_checked index (by omega) (by omega)
  else
    if cut : index < 430464 then
      exact segment_sound _ 430336 128 Restriction0840_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 430464 128 Restriction0840_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
