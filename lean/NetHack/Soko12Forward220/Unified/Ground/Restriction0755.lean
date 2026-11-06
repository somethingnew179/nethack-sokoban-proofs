import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0755_0_checked : (List.range' 386560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0755_1_checked : (List.range' 386688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0755_2_checked : (List.range' 386816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0755_3_checked : (List.range' 386944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0755_range (index : Nat) (lower : 386560 ≤ index) (upper : index < 387072) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 386816 then
    if cut : index < 386688 then
      exact segment_sound _ 386560 128 Restriction0755_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 386688 128 Restriction0755_1_checked index (by omega) (by omega)
  else
    if cut : index < 386944 then
      exact segment_sound _ 386816 128 Restriction0755_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 386944 128 Restriction0755_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
