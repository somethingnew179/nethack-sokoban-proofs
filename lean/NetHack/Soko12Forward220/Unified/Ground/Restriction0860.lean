import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0860_0_checked : (List.range' 440320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0860_1_checked : (List.range' 440448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0860_2_checked : (List.range' 440576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0860_3_checked : (List.range' 440704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0860_range (index : Nat) (lower : 440320 ≤ index) (upper : index < 440832) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 440576 then
    if cut : index < 440448 then
      exact segment_sound _ 440320 128 Restriction0860_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 440448 128 Restriction0860_1_checked index (by omega) (by omega)
  else
    if cut : index < 440704 then
      exact segment_sound _ 440576 128 Restriction0860_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 440704 128 Restriction0860_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
