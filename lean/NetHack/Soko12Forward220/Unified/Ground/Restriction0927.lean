import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0927_0_checked : (List.range' 474624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0927_1_checked : (List.range' 474752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0927_2_checked : (List.range' 474880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0927_3_checked : (List.range' 475008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0927_range (index : Nat) (lower : 474624 ≤ index) (upper : index < 475136) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 474880 then
    if cut : index < 474752 then
      exact segment_sound _ 474624 128 Restriction0927_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 474752 128 Restriction0927_1_checked index (by omega) (by omega)
  else
    if cut : index < 475008 then
      exact segment_sound _ 474880 128 Restriction0927_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 475008 128 Restriction0927_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
