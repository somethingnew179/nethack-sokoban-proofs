import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0939_0_checked : (List.range' 480768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0939_1_checked : (List.range' 480896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0939_2_checked : (List.range' 481024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0939_3_checked : (List.range' 481152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0939_range (index : Nat) (lower : 480768 ≤ index) (upper : index < 481280) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 481024 then
    if cut : index < 480896 then
      exact segment_sound _ 480768 128 Restriction0939_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 480896 128 Restriction0939_1_checked index (by omega) (by omega)
  else
    if cut : index < 481152 then
      exact segment_sound _ 481024 128 Restriction0939_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 481152 128 Restriction0939_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
