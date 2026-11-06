import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0836_0_checked : (List.range' 428032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0836_1_checked : (List.range' 428160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0836_2_checked : (List.range' 428288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0836_3_checked : (List.range' 428416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0836_range (index : Nat) (lower : 428032 ≤ index) (upper : index < 428544) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 428288 then
    if cut : index < 428160 then
      exact segment_sound _ 428032 128 Restriction0836_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 428160 128 Restriction0836_1_checked index (by omega) (by omega)
  else
    if cut : index < 428416 then
      exact segment_sound _ 428288 128 Restriction0836_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 428416 128 Restriction0836_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
