import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0937_0_checked : (List.range' 479744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0937_1_checked : (List.range' 479872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0937_2_checked : (List.range' 480000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0937_3_checked : (List.range' 480128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0937_range (index : Nat) (lower : 479744 ≤ index) (upper : index < 480256) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 480000 then
    if cut : index < 479872 then
      exact segment_sound _ 479744 128 Restriction0937_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 479872 128 Restriction0937_1_checked index (by omega) (by omega)
  else
    if cut : index < 480128 then
      exact segment_sound _ 480000 128 Restriction0937_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 480128 128 Restriction0937_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
