import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1866_0_checked : (List.range' 955392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1866_1_checked : (List.range' 955520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1866_2_checked : (List.range' 955648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1866_3_checked : (List.range' 955776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1866_range (index : Nat) (lower : 955392 ≤ index) (upper : index < 955904) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 955648 then
    if cut : index < 955520 then
      exact segment_sound _ 955392 128 Restriction1866_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 955520 128 Restriction1866_1_checked index (by omega) (by omega)
  else
    if cut : index < 955776 then
      exact segment_sound _ 955648 128 Restriction1866_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 955776 128 Restriction1866_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
