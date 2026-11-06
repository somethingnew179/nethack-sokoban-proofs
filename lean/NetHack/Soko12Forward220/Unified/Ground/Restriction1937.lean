import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1937_0_checked : (List.range' 991744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1937_1_checked : (List.range' 991872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1937_2_checked : (List.range' 992000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1937_3_checked : (List.range' 992128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1937_range (index : Nat) (lower : 991744 ≤ index) (upper : index < 992256) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 992000 then
    if cut : index < 991872 then
      exact segment_sound _ 991744 128 Restriction1937_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 991872 128 Restriction1937_1_checked index (by omega) (by omega)
  else
    if cut : index < 992128 then
      exact segment_sound _ 992000 128 Restriction1937_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 992128 128 Restriction1937_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
