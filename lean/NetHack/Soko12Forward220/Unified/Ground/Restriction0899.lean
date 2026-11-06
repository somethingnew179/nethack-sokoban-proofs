import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0899_0_checked : (List.range' 460288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0899_1_checked : (List.range' 460416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0899_2_checked : (List.range' 460544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0899_3_checked : (List.range' 460672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0899_range (index : Nat) (lower : 460288 ≤ index) (upper : index < 460800) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 460544 then
    if cut : index < 460416 then
      exact segment_sound _ 460288 128 Restriction0899_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 460416 128 Restriction0899_1_checked index (by omega) (by omega)
  else
    if cut : index < 460672 then
      exact segment_sound _ 460544 128 Restriction0899_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 460672 128 Restriction0899_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
