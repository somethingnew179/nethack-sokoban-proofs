import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1619_0_checked : (List.range' 828928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1619_1_checked : (List.range' 829056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1619_2_checked : (List.range' 829184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1619_3_checked : (List.range' 829312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1619_range (index : Nat) (lower : 828928 ≤ index) (upper : index < 829440) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 829184 then
    if cut : index < 829056 then
      exact segment_sound _ 828928 128 Restriction1619_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 829056 128 Restriction1619_1_checked index (by omega) (by omega)
  else
    if cut : index < 829312 then
      exact segment_sound _ 829184 128 Restriction1619_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 829312 128 Restriction1619_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
