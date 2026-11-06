import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0875_0_checked : (List.range' 448000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0875_1_checked : (List.range' 448128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0875_2_checked : (List.range' 448256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0875_3_checked : (List.range' 448384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0875_range (index : Nat) (lower : 448000 ≤ index) (upper : index < 448512) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 448256 then
    if cut : index < 448128 then
      exact segment_sound _ 448000 128 Restriction0875_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 448128 128 Restriction0875_1_checked index (by omega) (by omega)
  else
    if cut : index < 448384 then
      exact segment_sound _ 448256 128 Restriction0875_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 448384 128 Restriction0875_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
