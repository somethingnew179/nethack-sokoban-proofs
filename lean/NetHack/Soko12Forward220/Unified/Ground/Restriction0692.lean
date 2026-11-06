import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0692_0_checked : (List.range' 354304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0692_1_checked : (List.range' 354432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0692_2_checked : (List.range' 354560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0692_3_checked : (List.range' 354688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0692_range (index : Nat) (lower : 354304 ≤ index) (upper : index < 354816) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 354560 then
    if cut : index < 354432 then
      exact segment_sound _ 354304 128 Restriction0692_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 354432 128 Restriction0692_1_checked index (by omega) (by omega)
  else
    if cut : index < 354688 then
      exact segment_sound _ 354560 128 Restriction0692_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 354688 128 Restriction0692_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
