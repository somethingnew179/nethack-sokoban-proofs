import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0043_0_checked : (List.range' 22016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0043_1_checked : (List.range' 22144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0043_2_checked : (List.range' 22272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0043_3_checked : (List.range' 22400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0043_range (index : Nat) (lower : 22016 ≤ index) (upper : index < 22528) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 22272 then
    if cut : index < 22144 then
      exact segment_sound _ 22016 128 Restriction0043_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 22144 128 Restriction0043_1_checked index (by omega) (by omega)
  else
    if cut : index < 22400 then
      exact segment_sound _ 22272 128 Restriction0043_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 22400 128 Restriction0043_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
