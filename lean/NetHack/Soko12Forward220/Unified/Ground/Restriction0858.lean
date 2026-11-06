import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0858_0_checked : (List.range' 439296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0858_1_checked : (List.range' 439424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0858_2_checked : (List.range' 439552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0858_3_checked : (List.range' 439680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0858_range (index : Nat) (lower : 439296 ≤ index) (upper : index < 439808) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 439552 then
    if cut : index < 439424 then
      exact segment_sound _ 439296 128 Restriction0858_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 439424 128 Restriction0858_1_checked index (by omega) (by omega)
  else
    if cut : index < 439680 then
      exact segment_sound _ 439552 128 Restriction0858_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 439680 128 Restriction0858_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
