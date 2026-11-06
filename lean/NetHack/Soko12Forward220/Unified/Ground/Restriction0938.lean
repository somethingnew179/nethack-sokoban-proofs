import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0938_0_checked : (List.range' 480256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0938_1_checked : (List.range' 480384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0938_2_checked : (List.range' 480512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0938_3_checked : (List.range' 480640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0938_range (index : Nat) (lower : 480256 ≤ index) (upper : index < 480768) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 480512 then
    if cut : index < 480384 then
      exact segment_sound _ 480256 128 Restriction0938_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 480384 128 Restriction0938_1_checked index (by omega) (by omega)
  else
    if cut : index < 480640 then
      exact segment_sound _ 480512 128 Restriction0938_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 480640 128 Restriction0938_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
