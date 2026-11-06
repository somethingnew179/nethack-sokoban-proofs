import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0683_0_checked : (List.range' 349696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0683_1_checked : (List.range' 349824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0683_2_checked : (List.range' 349952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0683_3_checked : (List.range' 350080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0683_range (index : Nat) (lower : 349696 ≤ index) (upper : index < 350208) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 349952 then
    if cut : index < 349824 then
      exact segment_sound _ 349696 128 Restriction0683_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 349824 128 Restriction0683_1_checked index (by omega) (by omega)
  else
    if cut : index < 350080 then
      exact segment_sound _ 349952 128 Restriction0683_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 350080 128 Restriction0683_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
