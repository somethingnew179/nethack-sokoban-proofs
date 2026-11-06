/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions40
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub4920 (p : Pattern) : d25 (change p 161 (some 162)) = d25 p := by
  change (if p 204 then d12 (change p 161 (some 162)) else d24 (change p 161 (some 162))) = d25 p
  rw [sub4890, sub4919]
  rfl
theorem sub4921 (p : Pattern) : d26 (change p 161 (some 162)) = d26 p := by
  change (if p 182 then d25 (change p 161 (some 162)) else d24 (change p 161 (some 162))) = d26 p
  rw [sub4920, sub4919]
  rfl
theorem sub4922 (p : Pattern) : d55 (change p 161 (some 162)) = d55 p := by
  change (if p 163 then d26 (change p 161 (some 162)) else d20 (change p 161 (some 162))) = d55 p
  rw [sub4921, sub4899]
  rfl
theorem sub4923 (p : Pattern) : d56 (change p 161 (some 162)) = d55 p := by
  change d55 (change p 161 (some 162)) = d55 p
  exact sub4922 p
theorem sub4924 (p : Pattern) : d794 (change p 161 (some 162)) = d55 p := by
  change d56 (change p 161 (some 162)) = d55 p
  exact sub4923 p
theorem sub4925 (p : Pattern) : d797 (change p 161 (some 162)) = d797 p := by
  change (if p 182 then d36 (change p 161 (some 162)) else d18 (change p 161 (some 162))) = d797 p
  rw [sub4911, sub4897]
  rfl
theorem sub4926 (p : Pattern) : d11 (change p 161 (some 162)) = d11 p := by
  rfl
theorem sub4927 (p : Pattern) : d39 (change p 161 (some 162)) = d39 p := by
  change (if p 247 then d12 (change p 161 (some 162)) else d11 (change p 161 (some 162))) = d39 p
  rw [sub4890, sub4926]
  rfl
theorem sub4928 (p : Pattern) : d40 (change p 161 (some 162)) = d40 p := by
  change (if p 246 then d39 (change p 161 (some 162)) else d11 (change p 161 (some 162))) = d40 p
  rw [sub4927, sub4926]
  rfl
theorem sub4929 (p : Pattern) : d41 (change p 161 (some 162)) = d41 p := by
  change (if p 204 then d12 (change p 161 (some 162)) else d40 (change p 161 (some 162))) = d41 p
  rw [sub4890, sub4928]
  rfl
theorem sub4930 (p : Pattern) : d62 (change p 161 (some 162)) = d62 p := by
  change (if p 182 then d41 (change p 161 (some 162)) else d40 (change p 161 (some 162))) = d62 p
  rw [sub4929, sub4928]
  rfl
theorem sub4931 (p : Pattern) : d798 (change p 161 (some 162)) = d798 p := by
  change (if p 163 then d62 (change p 161 (some 162)) else d797 (change p 161 (some 162))) = d798 p
  rw [sub4930, sub4925]
  rfl
theorem sub4932 (p : Pattern) : d799 (change p 161 (some 162)) = d798 p := by
  change d798 (change p 161 (some 162)) = d798 p
  exact sub4931 p
theorem sub4933 (p : Pattern) : d800 (change p 161 (some 162)) = d798 p := by
  change d799 (change p 161 (some 162)) = d798 p
  exact sub4932 p
theorem sub4934 (p : Pattern) : d801 (change p 161 (some 162)) = d4620 p := by
  change (if p 160 then d800 (change p 161 (some 162)) else d794 (change p 161 (some 162))) = d4620 p
  rw [sub4933, sub4924]
  rfl
theorem sub4935 (p : Pattern) : d802 (change p 161 (some 162)) = d4621 p := by
  change (if p 141 then d801 (change p 161 (some 162)) else d793 (change p 161 (some 162))) = d4621 p
  rw [sub4934, sub4916]
  rfl
theorem sub4936 (p : Pattern) : d803 (change p 161 (some 162)) = d21 p := by
  change d22 (change p 161 (some 162)) = d21 p
  exact sub4901 p
theorem sub4937 (p : Pattern) : d804 (change p 161 (some 162)) = d79 p := by
  change d79 (change p 161 (some 162)) = d79 p
  exact sub4913 p
theorem sub4938 (p : Pattern) : d805 (change p 161 (some 162)) = d79 p := by
  change d804 (change p 161 (some 162)) = d79 p
  exact sub4937 p
theorem sub4939 (p : Pattern) : d806 (change p 161 (some 162)) = d4619 p := by
  change (if p 160 then d805 (change p 161 (some 162)) else d803 (change p 161 (some 162))) = d4619 p
  rw [sub4938, sub4936]
  rfl
theorem sub4940 (p : Pattern) : d807 (change p 161 (some 162)) = d55 p := by
  change d56 (change p 161 (some 162)) = d55 p
  exact sub4923 p
theorem sub4941 (p : Pattern) : d809 (change p 161 (some 162)) = d809 p := by
  change (if p 163 then d62 (change p 161 (some 162)) else d78 (change p 161 (some 162))) = d809 p
  rw [sub4930, sub4912]
  rfl
theorem sub4942 (p : Pattern) : d810 (change p 161 (some 162)) = d809 p := by
  change d809 (change p 161 (some 162)) = d809 p
  exact sub4941 p
theorem sub4943 (p : Pattern) : d811 (change p 161 (some 162)) = d809 p := by
  change d810 (change p 161 (some 162)) = d809 p
  exact sub4942 p
theorem sub4944 (p : Pattern) : d812 (change p 161 (some 162)) = d4622 p := by
  change (if p 160 then d811 (change p 161 (some 162)) else d807 (change p 161 (some 162))) = d4622 p
  rw [sub4943, sub4940]
  rfl
theorem sub4945 (p : Pattern) : d813 (change p 161 (some 162)) = d4623 p := by
  change (if p 141 then d812 (change p 161 (some 162)) else d806 (change p 161 (some 162))) = d4623 p
  rw [sub4944, sub4939]
  rfl
theorem sub4946 (p : Pattern) : d814 (change p 161 (some 162)) = d4624 p := by
  change (if p 138 then d813 (change p 161 (some 162)) else d802 (change p 161 (some 162))) = d4624 p
  rw [sub4945, sub4935]
  rfl
theorem sub4947 (p : Pattern) : d815 (change p 161 (some 162)) = d21 p := by
  change d22 (change p 161 (some 162)) = d21 p
  exact sub4901 p
theorem sub4948 (p : Pattern) : d816 (change p 161 (some 162)) = d4619 p := by
  change (if p 160 then d805 (change p 161 (some 162)) else d815 (change p 161 (some 162))) = d4619 p
  rw [sub4938, sub4947]
  rfl
theorem sub4949 (p : Pattern) : d817 (change p 161 (some 162)) = d55 p := by
  change d56 (change p 161 (some 162)) = d55 p
  exact sub4923 p
theorem sub4950 (p : Pattern) : d818 (change p 161 (some 162)) = d4622 p := by
  change (if p 160 then d811 (change p 161 (some 162)) else d817 (change p 161 (some 162))) = d4622 p
  rw [sub4943, sub4949]
  rfl
theorem sub4951 (p : Pattern) : d819 (change p 161 (some 162)) = d4623 p := by
  change (if p 141 then d818 (change p 161 (some 162)) else d816 (change p 161 (some 162))) = d4623 p
  rw [sub4950, sub4948]
  rfl
theorem sub4952 (p : Pattern) : d63 (change p 161 (some 162)) = d63 p := by
  change (if p 163 then d12 (change p 161 (some 162)) else d62 (change p 161 (some 162))) = d63 p
  rw [sub4890, sub4930]
  rfl
theorem sub4953 (p : Pattern) : d90 (change p 161 (some 162)) = d63 p := by
  change d63 (change p 161 (some 162)) = d63 p
  exact sub4952 p
theorem sub4954 (p : Pattern) : d820 (change p 161 (some 162)) = d63 p := by
  change d90 (change p 161 (some 162)) = d63 p
  exact sub4953 p
theorem sub4955 (p : Pattern) : d91 (change p 161 (some 162)) = d12 p := by
  change d12 (change p 161 (some 162)) = d12 p
  exact sub4890 p
theorem sub4956 (p : Pattern) : d93 (change p 161 (some 162)) = d12 p := by
  change d91 (change p 161 (some 162)) = d12 p
  exact sub4955 p
theorem sub4957 (p : Pattern) : d821 (change p 161 (some 162)) = d4625 p := by
  change (if p 160 then d93 (change p 161 (some 162)) else d820 (change p 161 (some 162))) = d4625 p
  rw [sub4956, sub4954]
  rfl
theorem sub4958 (p : Pattern) : d95 (change p 161 (some 162)) = d12 p := by
  change (if p 160 then d12 (change p 161 (some 162)) else d93 (change p 161 (some 162))) = d12 p
  rw [sub4890, sub4956]
  simp only [ite_self]
theorem sub4959 (p : Pattern) : d822 (change p 161 (some 162)) = d4626 p := by
  change (if p 141 then d95 (change p 161 (some 162)) else d821 (change p 161 (some 162))) = d4626 p
  rw [sub4958, sub4957]
  rfl
theorem sub4960 (p : Pattern) : d823 (change p 161 (some 162)) = d4627 p := by
  change (if p 138 then d822 (change p 161 (some 162)) else d819 (change p 161 (some 162))) = d4627 p
  rw [sub4959, sub4951]
  rfl
theorem sub4961 (p : Pattern) : d824 (change p 161 (some 162)) = d4628 p := by
  change (if p 116 then d823 (change p 161 (some 162)) else d814 (change p 161 (some 162))) = d4628 p
  rw [sub4960, sub4946]
  rfl
theorem sub4962 (p : Pattern) : d825 (change p 161 (some 162)) = d21 p := by
  change d22 (change p 161 (some 162)) = d21 p
  exact sub4901 p
theorem sub4963 (p : Pattern) : d826 (change p 161 (some 162)) = d79 p := by
  change d791 (change p 161 (some 162)) = d79 p
  exact sub4914 p
theorem sub4964 (p : Pattern) : d827 (change p 161 (some 162)) = d4619 p := by
  change (if p 160 then d826 (change p 161 (some 162)) else d825 (change p 161 (some 162))) = d4619 p
  rw [sub4963, sub4962]
  rfl
theorem sub4965 (p : Pattern) : d828 (change p 161 (some 162)) = d55 p := by
  change d56 (change p 161 (some 162)) = d55 p
  exact sub4923 p
theorem sub4966 (p : Pattern) : d829 (change p 161 (some 162)) = d4620 p := by
  change (if p 160 then d800 (change p 161 (some 162)) else d828 (change p 161 (some 162))) = d4620 p
  rw [sub4933, sub4965]
  rfl
theorem sub4967 (p : Pattern) : d830 (change p 161 (some 162)) = d4621 p := by
  change (if p 141 then d829 (change p 161 (some 162)) else d827 (change p 161 (some 162))) = d4621 p
  rw [sub4966, sub4964]
  rfl
theorem sub4968 (p : Pattern) : d831 (change p 161 (some 162)) = d21 p := by
  change d22 (change p 161 (some 162)) = d21 p
  exact sub4901 p
theorem sub4969 (p : Pattern) : d832 (change p 161 (some 162)) = d4619 p := by
  change (if p 160 then d805 (change p 161 (some 162)) else d831 (change p 161 (some 162))) = d4619 p
  rw [sub4938, sub4968]
  rfl
theorem sub4970 (p : Pattern) : d833 (change p 161 (some 162)) = d4623 p := by
  change (if p 141 then d812 (change p 161 (some 162)) else d832 (change p 161 (some 162))) = d4623 p
  rw [sub4944, sub4969]
  rfl
theorem sub4971 (p : Pattern) : d834 (change p 161 (some 162)) = d4624 p := by
  change (if p 138 then d833 (change p 161 (some 162)) else d830 (change p 161 (some 162))) = d4624 p
  rw [sub4970, sub4967]
  rfl
theorem sub4972 (p : Pattern) : d835 (change p 161 (some 162)) = d4629 p := by
  change (if p 138 then d12 (change p 161 (some 162)) else d833 (change p 161 (some 162))) = d4629 p
  rw [sub4890, sub4970]
  rfl
theorem sub4973 (p : Pattern) : d836 (change p 161 (some 162)) = d4630 p := by
  change (if p 116 then d835 (change p 161 (some 162)) else d834 (change p 161 (some 162))) = d4630 p
  rw [sub4972, sub4971]
  rfl
theorem sub4974 (p : Pattern) : d837 (change p 161 (some 162)) = d4631 p := by
  change (if p 115 then d836 (change p 161 (some 162)) else d824 (change p 161 (some 162))) = d4631 p
  rw [sub4973, sub4961]
  rfl
theorem sub4975 (p : Pattern) : d838 (change p 161 (some 162)) = d21 p := by
  change d22 (change p 161 (some 162)) = d21 p
  exact sub4901 p
theorem sub4976 (p : Pattern) : d839 (change p 161 (some 162)) = d4619 p := by
  change (if p 160 then d826 (change p 161 (some 162)) else d838 (change p 161 (some 162))) = d4619 p
  rw [sub4963, sub4975]
  rfl
theorem sub4977 (p : Pattern) : d840 (change p 161 (some 162)) = d55 p := by
  change d56 (change p 161 (some 162)) = d55 p
  exact sub4923 p
theorem sub4978 (p : Pattern) : d841 (change p 161 (some 162)) = d4620 p := by
  change (if p 160 then d800 (change p 161 (some 162)) else d840 (change p 161 (some 162))) = d4620 p
  rw [sub4933, sub4977]
  rfl
theorem sub4979 (p : Pattern) : d842 (change p 161 (some 162)) = d4621 p := by
  change (if p 141 then d841 (change p 161 (some 162)) else d839 (change p 161 (some 162))) = d4621 p
  rw [sub4978, sub4976]
  rfl
theorem sub4980 (p : Pattern) : d843 (change p 161 (some 162)) = d21 p := by
  change d22 (change p 161 (some 162)) = d21 p
  exact sub4901 p
theorem sub4981 (p : Pattern) : d844 (change p 161 (some 162)) = d4619 p := by
  change (if p 160 then d805 (change p 161 (some 162)) else d843 (change p 161 (some 162))) = d4619 p
  rw [sub4938, sub4980]
  rfl
theorem sub4982 (p : Pattern) : d845 (change p 161 (some 162)) = d4623 p := by
  change (if p 141 then d812 (change p 161 (some 162)) else d844 (change p 161 (some 162))) = d4623 p
  rw [sub4944, sub4981]
  rfl
theorem sub4983 (p : Pattern) : d846 (change p 161 (some 162)) = d4624 p := by
  change (if p 138 then d845 (change p 161 (some 162)) else d842 (change p 161 (some 162))) = d4624 p
  rw [sub4982, sub4979]
  rfl
theorem sub4984 (p : Pattern) : d847 (change p 161 (some 162)) = d4627 p := by
  change (if p 138 then d822 (change p 161 (some 162)) else d813 (change p 161 (some 162))) = d4627 p
  rw [sub4959, sub4945]
  rfl
theorem sub4985 (p : Pattern) : d848 (change p 161 (some 162)) = d4628 p := by
  change (if p 116 then d847 (change p 161 (some 162)) else d846 (change p 161 (some 162))) = d4628 p
  rw [sub4984, sub4983]
  rfl
theorem sub4986 (p : Pattern) : d849 (change p 161 (some 162)) = d4619 p := by
  change (if p 160 then d826 (change p 161 (some 162)) else d815 (change p 161 (some 162))) = d4619 p
  rw [sub4963, sub4947]
  rfl
theorem sub4987 (p : Pattern) : d850 (change p 161 (some 162)) = d4620 p := by
  change (if p 160 then d800 (change p 161 (some 162)) else d817 (change p 161 (some 162))) = d4620 p
  rw [sub4933, sub4949]
  rfl
theorem sub4988 (p : Pattern) : d851 (change p 161 (some 162)) = d4621 p := by
  change (if p 141 then d850 (change p 161 (some 162)) else d849 (change p 161 (some 162))) = d4621 p
  rw [sub4987, sub4986]
  rfl
theorem sub4989 (p : Pattern) : d852 (change p 161 (some 162)) = d4624 p := by
  change (if p 138 then d833 (change p 161 (some 162)) else d851 (change p 161 (some 162))) = d4624 p
  rw [sub4970, sub4988]
  rfl
theorem sub4990 (p : Pattern) : d853 (change p 161 (some 162)) = d4630 p := by
  change (if p 116 then d835 (change p 161 (some 162)) else d852 (change p 161 (some 162))) = d4630 p
  rw [sub4972, sub4989]
  rfl
theorem sub4991 (p : Pattern) : d854 (change p 161 (some 162)) = d4631 p := by
  change (if p 115 then d853 (change p 161 (some 162)) else d848 (change p 161 (some 162))) = d4631 p
  rw [sub4990, sub4985]
  rfl
theorem sub4992 (p : Pattern) : d855 (change p 161 (some 162)) = d4631 p := by
  change (if p 71 then d854 (change p 161 (some 162)) else d837 (change p 161 (some 162))) = d4631 p
  rw [sub4991, sub4974]
  simp only [ite_self]
theorem sub4993 (p : Pattern) : d1 (change p 161 (some 162)) = d1 p := by
  rfl
theorem sub4994 (p : Pattern) : d102 (change p 161 (some 162)) = d102 p := by
  change (if p 247 then d12 (change p 161 (some 162)) else d1 (change p 161 (some 162))) = d102 p
  rw [sub4890, sub4993]
  rfl
theorem sub4995 (p : Pattern) : d103 (change p 161 (some 162)) = d103 p := by
  change (if p 246 then d102 (change p 161 (some 162)) else d1 (change p 161 (some 162))) = d103 p
  rw [sub4994, sub4993]
  rfl
theorem sub4996 (p : Pattern) : d104 (change p 161 (some 162)) = d104 p := by
  change (if p 204 then d12 (change p 161 (some 162)) else d103 (change p 161 (some 162))) = d104 p
  rw [sub4890, sub4995]
  rfl
theorem sub4997 (p : Pattern) : d105 (change p 161 (some 162)) = d105 p := by
  change (if p 182 then d104 (change p 161 (some 162)) else d103 (change p 161 (some 162))) = d105 p
  rw [sub4996, sub4995]
  rfl
theorem sub4998 (p : Pattern) : d5 (change p 161 (some 162)) = d5 p := by
  rfl
theorem sub4999 (p : Pattern) : d106 (change p 161 (some 162)) = d106 p := by
  change (if p 247 then d12 (change p 161 (some 162)) else d5 (change p 161 (some 162))) = d106 p
  rw [sub4890, sub4998]
  rfl
theorem sub5000 (p : Pattern) : d107 (change p 161 (some 162)) = d107 p := by
  change (if p 246 then d106 (change p 161 (some 162)) else d5 (change p 161 (some 162))) = d107 p
  rw [sub4999, sub4998]
  rfl
theorem sub5001 (p : Pattern) : d108 (change p 161 (some 162)) = d108 p := by
  change (if p 204 then d12 (change p 161 (some 162)) else d107 (change p 161 (some 162))) = d108 p
  rw [sub4890, sub5000]
  rfl
theorem sub5002 (p : Pattern) : d109 (change p 161 (some 162)) = d109 p := by
  change (if p 182 then d108 (change p 161 (some 162)) else d107 (change p 161 (some 162))) = d109 p
  rw [sub5001, sub5000]
  rfl
theorem sub5003 (p : Pattern) : d110 (change p 161 (some 162)) = d110 p := by
  change (if p 163 then d109 (change p 161 (some 162)) else d105 (change p 161 (some 162))) = d110 p
  rw [sub5002, sub4997]
  rfl
theorem sub5004 (p : Pattern) : d111 (change p 161 (some 162)) = d110 p := by
  change d110 (change p 161 (some 162)) = d110 p
  exact sub5003 p
theorem sub5005 (p : Pattern) : d856 (change p 161 (some 162)) = d110 p := by
  change d111 (change p 161 (some 162)) = d110 p
  exact sub5004 p
theorem sub5006 (p : Pattern) : d3 (change p 161 (some 162)) = d3 p := by
  rfl
theorem sub5007 (p : Pattern) : d115 (change p 161 (some 162)) = d115 p := by
  change (if p 247 then d12 (change p 161 (some 162)) else d3 (change p 161 (some 162))) = d115 p
  rw [sub4890, sub5006]
  rfl
theorem sub5008 (p : Pattern) : d116 (change p 161 (some 162)) = d116 p := by
  change (if p 246 then d115 (change p 161 (some 162)) else d3 (change p 161 (some 162))) = d116 p
  rw [sub5007, sub5006]
  rfl
theorem sub5009 (p : Pattern) : d117 (change p 161 (some 162)) = d117 p := by
  change (if p 204 then d12 (change p 161 (some 162)) else d116 (change p 161 (some 162))) = d117 p
  rw [sub4890, sub5008]
  rfl
theorem sub5010 (p : Pattern) : d132 (change p 161 (some 162)) = d132 p := by
  change (if p 182 then d117 (change p 161 (some 162)) else d116 (change p 161 (some 162))) = d132 p
  rw [sub5009, sub5008]
  rfl
theorem sub5011 (p : Pattern) : d7 (change p 161 (some 162)) = d7 p := by
  rfl
theorem sub5012 (p : Pattern) : d119 (change p 161 (some 162)) = d119 p := by
  change (if p 247 then d12 (change p 161 (some 162)) else d7 (change p 161 (some 162))) = d119 p
  rw [sub4890, sub5011]
  rfl
theorem sub5013 (p : Pattern) : d120 (change p 161 (some 162)) = d120 p := by
  change (if p 246 then d119 (change p 161 (some 162)) else d7 (change p 161 (some 162))) = d120 p
  rw [sub5012, sub5011]
  rfl
theorem sub5014 (p : Pattern) : d121 (change p 161 (some 162)) = d121 p := by
  change (if p 204 then d12 (change p 161 (some 162)) else d120 (change p 161 (some 162))) = d121 p
  rw [sub4890, sub5013]
  rfl
theorem sub5015 (p : Pattern) : d148 (change p 161 (some 162)) = d148 p := by
  change (if p 182 then d121 (change p 161 (some 162)) else d120 (change p 161 (some 162))) = d148 p
  rw [sub5014, sub5013]
  rfl
theorem sub5016 (p : Pattern) : d149 (change p 161 (some 162)) = d149 p := by
  change (if p 163 then d148 (change p 161 (some 162)) else d132 (change p 161 (some 162))) = d149 p
  rw [sub5015, sub5010]
  rfl
theorem sub5017 (p : Pattern) : d857 (change p 161 (some 162)) = d149 p := by
  change d149 (change p 161 (some 162)) = d149 p
  exact sub5016 p
theorem sub5018 (p : Pattern) : d858 (change p 161 (some 162)) = d149 p := by
  change d857 (change p 161 (some 162)) = d149 p
  exact sub5017 p
theorem sub5019 (p : Pattern) : d859 (change p 161 (some 162)) = d4632 p := by
  change (if p 160 then d858 (change p 161 (some 162)) else d856 (change p 161 (some 162))) = d4632 p
  rw [sub5018, sub5005]
  rfl
theorem sub5020 (p : Pattern) : d10 (change p 161 (some 162)) = d10 p := by
  rfl
theorem sub5021 (p : Pattern) : d57 (change p 161 (some 162)) = d57 p := by
  change (if p 247 then d12 (change p 161 (some 162)) else d10 (change p 161 (some 162))) = d57 p
  rw [sub4890, sub5020]
  rfl
theorem sub5022 (p : Pattern) : d58 (change p 161 (some 162)) = d58 p := by
  change (if p 246 then d57 (change p 161 (some 162)) else d10 (change p 161 (some 162))) = d58 p
  rw [sub5021, sub5020]
  rfl
theorem sub5023 (p : Pattern) : d59 (change p 161 (some 162)) = d59 p := by
  change (if p 204 then d12 (change p 161 (some 162)) else d58 (change p 161 (some 162))) = d59 p
  rw [sub4890, sub5022]
  rfl
theorem sub5024 (p : Pattern) : d60 (change p 161 (some 162)) = d60 p := by
  change (if p 182 then d59 (change p 161 (some 162)) else d58 (change p 161 (some 162))) = d60 p
  rw [sub5023, sub5022]
  rfl
theorem sub5025 (p : Pattern) : d134 (change p 161 (some 162)) = d134 p := by
  change (if p 163 then d60 (change p 161 (some 162)) else d109 (change p 161 (some 162))) = d134 p
  rw [sub5024, sub5002]
  rfl
theorem sub5026 (p : Pattern) : d135 (change p 161 (some 162)) = d134 p := by
  change d134 (change p 161 (some 162)) = d134 p
  exact sub5025 p
theorem sub5027 (p : Pattern) : d860 (change p 161 (some 162)) = d134 p := by
  change d135 (change p 161 (some 162)) = d134 p
  exact sub5026 p
theorem sub5028 (p : Pattern) : d234 (change p 161 (some 162)) = d234 p := by
  change (if p 182 then d121 (change p 161 (some 162)) else d107 (change p 161 (some 162))) = d234 p
  rw [sub5014, sub5000]
  rfl
theorem sub5029 (p : Pattern) : d863 (change p 161 (some 162)) = d863 p := by
  change (if p 163 then d12 (change p 161 (some 162)) else d234 (change p 161 (some 162))) = d863 p
  rw [sub4890, sub5028]
  rfl
theorem sub5030 (p : Pattern) : d864 (change p 161 (some 162)) = d863 p := by
  change d863 (change p 161 (some 162)) = d863 p
  exact sub5029 p
theorem sub5031 (p : Pattern) : d865 (change p 161 (some 162)) = d863 p := by
  change d864 (change p 161 (some 162)) = d863 p
  exact sub5030 p
theorem sub5032 (p : Pattern) : d866 (change p 161 (some 162)) = d4633 p := by
  change (if p 160 then d865 (change p 161 (some 162)) else d860 (change p 161 (some 162))) = d4633 p
  rw [sub5031, sub5027]
  rfl
theorem sub5033 (p : Pattern) : d867 (change p 161 (some 162)) = d4634 p := by
  change (if p 141 then d866 (change p 161 (some 162)) else d859 (change p 161 (some 162))) = d4634 p
  rw [sub5032, sub5019]
  rfl
theorem sub5034 (p : Pattern) : d868 (change p 161 (some 162)) = d110 p := by
  change d111 (change p 161 (some 162)) = d110 p
  exact sub5004 p
theorem sub5035 (p : Pattern) : d869 (change p 161 (some 162)) = d149 p := by
  change d149 (change p 161 (some 162)) = d149 p
  exact sub5016 p
theorem sub5036 (p : Pattern) : d870 (change p 161 (some 162)) = d149 p := by
  change d869 (change p 161 (some 162)) = d149 p
  exact sub5035 p
theorem sub5037 (p : Pattern) : d871 (change p 161 (some 162)) = d4632 p := by
  change (if p 160 then d870 (change p 161 (some 162)) else d868 (change p 161 (some 162))) = d4632 p
  rw [sub5036, sub5034]
  rfl
theorem sub5038 (p : Pattern) : d872 (change p 161 (some 162)) = d134 p := by
  change d135 (change p 161 (some 162)) = d134 p
  exact sub5026 p
theorem sub5039 (p : Pattern) : d153 (change p 161 (some 162)) = d153 p := by
  change (if p 163 then d12 (change p 161 (some 162)) else d148 (change p 161 (some 162))) = d153 p
  rw [sub4890, sub5015]
  rfl
end NetHack.Sokoban22Refined85
