import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0458_0_checked : (List.range' 234496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0458_1_checked : (List.range' 234624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0458_2_checked : (List.range' 234752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0458_3_checked : (List.range' 234880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0458_range (index : Nat) (lower : 234496 ≤ index) (upper : index < 235008) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 234752 then
    if cut : index < 234624 then
      exact segment_sound _ 234496 128 Restriction0458_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 234624 128 Restriction0458_1_checked index (by omega) (by omega)
  else
    if cut : index < 234880 then
      exact segment_sound _ 234752 128 Restriction0458_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 234880 128 Restriction0458_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
