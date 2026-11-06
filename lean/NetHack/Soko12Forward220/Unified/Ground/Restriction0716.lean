import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0716_0_checked : (List.range' 366592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0716_1_checked : (List.range' 366720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0716_2_checked : (List.range' 366848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0716_3_checked : (List.range' 366976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0716_range (index : Nat) (lower : 366592 ≤ index) (upper : index < 367104) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 366848 then
    if cut : index < 366720 then
      exact segment_sound _ 366592 128 Restriction0716_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 366720 128 Restriction0716_1_checked index (by omega) (by omega)
  else
    if cut : index < 366976 then
      exact segment_sound _ 366848 128 Restriction0716_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 366976 128 Restriction0716_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
