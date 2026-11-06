import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1509_0_checked : (List.range' 772608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1509_1_checked : (List.range' 772736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1509_2_checked : (List.range' 772864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1509_3_checked : (List.range' 772992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1509_range (index : Nat) (lower : 772608 ≤ index) (upper : index < 773120) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 772864 then
    if cut : index < 772736 then
      exact segment_sound _ 772608 128 Restriction1509_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 772736 128 Restriction1509_1_checked index (by omega) (by omega)
  else
    if cut : index < 772992 then
      exact segment_sound _ 772864 128 Restriction1509_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 772992 128 Restriction1509_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
