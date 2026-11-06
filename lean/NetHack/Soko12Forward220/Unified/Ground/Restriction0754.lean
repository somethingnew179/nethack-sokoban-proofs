import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0754_0_checked : (List.range' 386048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0754_1_checked : (List.range' 386176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0754_2_checked : (List.range' 386304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0754_3_checked : (List.range' 386432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0754_range (index : Nat) (lower : 386048 ≤ index) (upper : index < 386560) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 386304 then
    if cut : index < 386176 then
      exact segment_sound _ 386048 128 Restriction0754_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 386176 128 Restriction0754_1_checked index (by omega) (by omega)
  else
    if cut : index < 386432 then
      exact segment_sound _ 386304 128 Restriction0754_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 386432 128 Restriction0754_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
