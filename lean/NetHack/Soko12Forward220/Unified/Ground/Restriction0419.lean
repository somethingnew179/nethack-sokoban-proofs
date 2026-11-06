import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0419_0_checked : (List.range' 214528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0419_1_checked : (List.range' 214656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0419_2_checked : (List.range' 214784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0419_3_checked : (List.range' 214912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0419_range (index : Nat) (lower : 214528 ≤ index) (upper : index < 215040) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 214784 then
    if cut : index < 214656 then
      exact segment_sound _ 214528 128 Restriction0419_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 214656 128 Restriction0419_1_checked index (by omega) (by omega)
  else
    if cut : index < 214912 then
      exact segment_sound _ 214784 128 Restriction0419_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 214912 128 Restriction0419_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
