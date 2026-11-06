import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0698_0_checked : (List.range' 357376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0698_1_checked : (List.range' 357504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0698_2_checked : (List.range' 357632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0698_3_checked : (List.range' 357760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0698_range (index : Nat) (lower : 357376 ≤ index) (upper : index < 357888) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 357632 then
    if cut : index < 357504 then
      exact segment_sound _ 357376 128 Restriction0698_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 357504 128 Restriction0698_1_checked index (by omega) (by omega)
  else
    if cut : index < 357760 then
      exact segment_sound _ 357632 128 Restriction0698_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 357760 128 Restriction0698_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
