import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0236_0_checked : (List.range' 120832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0236_1_checked : (List.range' 120960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0236_2_checked : (List.range' 121088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0236_3_checked : (List.range' 121216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0236_range (index : Nat) (lower : 120832 ≤ index) (upper : index < 121344) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 121088 then
    if cut : index < 120960 then
      exact segment_sound _ 120832 128 Restriction0236_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 120960 128 Restriction0236_1_checked index (by omega) (by omega)
  else
    if cut : index < 121216 then
      exact segment_sound _ 121088 128 Restriction0236_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 121216 128 Restriction0236_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
