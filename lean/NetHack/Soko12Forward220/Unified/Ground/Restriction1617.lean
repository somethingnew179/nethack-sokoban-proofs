import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1617_0_checked : (List.range' 827904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1617_1_checked : (List.range' 828032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1617_2_checked : (List.range' 828160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1617_3_checked : (List.range' 828288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1617_range (index : Nat) (lower : 827904 ≤ index) (upper : index < 828416) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 828160 then
    if cut : index < 828032 then
      exact segment_sound _ 827904 128 Restriction1617_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 828032 128 Restriction1617_1_checked index (by omega) (by omega)
  else
    if cut : index < 828288 then
      exact segment_sound _ 828160 128 Restriction1617_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 828288 128 Restriction1617_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
