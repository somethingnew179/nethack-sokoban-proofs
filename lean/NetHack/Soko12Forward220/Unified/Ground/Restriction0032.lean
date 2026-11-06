import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0032_0_checked : (List.range' 16384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0032_1_checked : (List.range' 16512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0032_2_checked : (List.range' 16640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0032_3_checked : (List.range' 16768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0032_range (index : Nat) (lower : 16384 ≤ index) (upper : index < 16896) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 16640 then
    if cut : index < 16512 then
      exact segment_sound _ 16384 128 Restriction0032_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 16512 128 Restriction0032_1_checked index (by omega) (by omega)
  else
    if cut : index < 16768 then
      exact segment_sound _ 16640 128 Restriction0032_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 16768 128 Restriction0032_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
