import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0857_0_checked : (List.range' 438784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0857_1_checked : (List.range' 438912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0857_2_checked : (List.range' 439040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0857_3_checked : (List.range' 439168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0857_range (index : Nat) (lower : 438784 ≤ index) (upper : index < 439296) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 439040 then
    if cut : index < 438912 then
      exact segment_sound _ 438784 128 Restriction0857_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 438912 128 Restriction0857_1_checked index (by omega) (by omega)
  else
    if cut : index < 439168 then
      exact segment_sound _ 439040 128 Restriction0857_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 439168 128 Restriction0857_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
