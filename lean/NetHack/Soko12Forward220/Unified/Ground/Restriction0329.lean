import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0329_0_checked : (List.range' 168448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0329_1_checked : (List.range' 168576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0329_2_checked : (List.range' 168704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0329_3_checked : (List.range' 168832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0329_range (index : Nat) (lower : 168448 ≤ index) (upper : index < 168960) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 168704 then
    if cut : index < 168576 then
      exact segment_sound _ 168448 128 Restriction0329_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 168576 128 Restriction0329_1_checked index (by omega) (by omega)
  else
    if cut : index < 168832 then
      exact segment_sound _ 168704 128 Restriction0329_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 168832 128 Restriction0329_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
