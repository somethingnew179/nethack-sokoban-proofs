import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1835_0_checked : (List.range' 939520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1835_1_checked : (List.range' 939648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1835_2_checked : (List.range' 939776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1835_3_checked : (List.range' 939904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1835_range (index : Nat) (lower : 939520 ≤ index) (upper : index < 940032) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 939776 then
    if cut : index < 939648 then
      exact segment_sound _ 939520 128 Restriction1835_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 939648 128 Restriction1835_1_checked index (by omega) (by omega)
  else
    if cut : index < 939904 then
      exact segment_sound _ 939776 128 Restriction1835_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 939904 128 Restriction1835_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
