import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0762_0_checked : (List.range' 390144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0762_1_checked : (List.range' 390272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0762_2_checked : (List.range' 390400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0762_3_checked : (List.range' 390528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0762_range (index : Nat) (lower : 390144 ≤ index) (upper : index < 390656) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 390400 then
    if cut : index < 390272 then
      exact segment_sound _ 390144 128 Restriction0762_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 390272 128 Restriction0762_1_checked index (by omega) (by omega)
  else
    if cut : index < 390528 then
      exact segment_sound _ 390400 128 Restriction0762_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 390528 128 Restriction0762_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
