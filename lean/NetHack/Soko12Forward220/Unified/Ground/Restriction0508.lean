import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0508_0_checked : (List.range' 260096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0508_1_checked : (List.range' 260224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0508_2_checked : (List.range' 260352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0508_3_checked : (List.range' 260480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0508_range (index : Nat) (lower : 260096 ≤ index) (upper : index < 260608) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 260352 then
    if cut : index < 260224 then
      exact segment_sound _ 260096 128 Restriction0508_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 260224 128 Restriction0508_1_checked index (by omega) (by omega)
  else
    if cut : index < 260480 then
      exact segment_sound _ 260352 128 Restriction0508_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 260480 128 Restriction0508_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
