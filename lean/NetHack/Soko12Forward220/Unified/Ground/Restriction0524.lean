import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0524_0_checked : (List.range' 268288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0524_1_checked : (List.range' 268416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0524_2_checked : (List.range' 268544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0524_3_checked : (List.range' 268672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0524_range (index : Nat) (lower : 268288 ≤ index) (upper : index < 268800) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 268544 then
    if cut : index < 268416 then
      exact segment_sound _ 268288 128 Restriction0524_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 268416 128 Restriction0524_1_checked index (by omega) (by omega)
  else
    if cut : index < 268672 then
      exact segment_sound _ 268544 128 Restriction0524_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 268672 128 Restriction0524_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
