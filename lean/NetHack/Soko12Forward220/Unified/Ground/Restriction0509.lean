import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0509_0_checked : (List.range' 260608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0509_1_checked : (List.range' 260736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0509_2_checked : (List.range' 260864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0509_3_checked : (List.range' 260992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0509_range (index : Nat) (lower : 260608 ≤ index) (upper : index < 261120) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 260864 then
    if cut : index < 260736 then
      exact segment_sound _ 260608 128 Restriction0509_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 260736 128 Restriction0509_1_checked index (by omega) (by omega)
  else
    if cut : index < 260992 then
      exact segment_sound _ 260864 128 Restriction0509_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 260992 128 Restriction0509_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
