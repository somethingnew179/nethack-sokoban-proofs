/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions32
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s4950 (pattern : Twelve) : d104 (change pattern 12 5) = d3170 pattern := by
  change (if pattern.j then d96 (change pattern 12 5) else d95 (change pattern 12 5)) = d3170 pattern
  rw [s4949, s4935]
  rfl
theorem s4951 (pattern : Twelve) : d105 (change pattern 12 5) = d3171 pattern := by
  change (if pattern.j then d6 (change pattern 12 5) else d94 (change pattern 12 5)) = d3171 pattern
  rw [s4902, s4928]
  rfl
theorem s4952 (pattern : Twelve) : d111 (change pattern 12 5) = d3172 pattern := by
  change (if pattern.d then d105 (change pattern 12 5) else d104 (change pattern 12 5)) = d3172 pattern
  rw [s4951, s4950]
  rfl
theorem s4953 (pattern : Twelve) : d114 (change pattern 12 5) = d3173 pattern := by
  change (if pattern.c then d111 (change pattern 12 5) else d110 (change pattern 12 5)) = d3173 pattern
  rw [s4952, s4930]
  rfl
theorem s4954 (pattern : Twelve) : d120 (change pattern 12 5) = d120 pattern := by
  change (if pattern.i then d25 (change pattern 12 5) else d17 (change pattern 12 5)) = d120 pattern
  rw [s4945, s4889]
  rfl
theorem s4955 (pattern : Twelve) : d129 (change pattern 12 5) = d129 pattern := by
  change (if pattern.h then d29 (change pattern 12 5) else d120 (change pattern 12 5)) = d129 pattern
  rw [s4903, s4954]
  rfl
theorem s4956 (pattern : Twelve) : d136 (change pattern 12 5) = d129 pattern := by
  change d129 (change pattern 12 5) = d129 pattern
  exact s4955 pattern
theorem s4957 (pattern : Twelve) : d144 (change pattern 12 5) = d3174 pattern := by
  change (if pattern.e then d136 (change pattern 12 5) else d72 (change pattern 12 5)) = d3174 pattern
  rw [s4956, s4892]
  rfl
theorem s4958 (pattern : Twelve) : d121 (change pattern 12 5) = d121 pattern := by
  change (if pattern.i then d23 (change pattern 12 5) else d0 (change pattern 12 5)) = d121 pattern
  rw [s4916, s4885]
  rfl
theorem s4959 (pattern : Twelve) : d130 (change pattern 12 5) = d130 pattern := by
  change (if pattern.h then d36 (change pattern 12 5) else d121 (change pattern 12 5)) = d130 pattern
  rw [s4924, s4958]
  rfl
theorem s4960 (pattern : Twelve) : d137 (change pattern 12 5) = d130 pattern := by
  change d130 (change pattern 12 5) = d130 pattern
  exact s4959 pattern
theorem s4961 (pattern : Twelve) : d138 (change pattern 12 5) = d129 pattern := by
  change d129 (change pattern 12 5) = d129 pattern
  exact s4955 pattern
theorem s4962 (pattern : Twelve) : d145 (change pattern 12 5) = d3175 pattern := by
  change (if pattern.e then d138 (change pattern 12 5) else d137 (change pattern 12 5)) = d3175 pattern
  rw [s4961, s4960]
  rfl
theorem s4963 (pattern : Twelve) : d149 (change pattern 12 5) = d3176 pattern := by
  change (if pattern.j then d145 (change pattern 12 5) else d144 (change pattern 12 5)) = d3176 pattern
  rw [s4962, s4957]
  rfl
theorem s4964 (pattern : Twelve) : d139 (change pattern 12 5) = d130 pattern := by
  change d130 (change pattern 12 5) = d130 pattern
  exact s4959 pattern
theorem s4965 (pattern : Twelve) : d146 (change pattern 12 5) = d3175 pattern := by
  change (if pattern.e then d138 (change pattern 12 5) else d139 (change pattern 12 5)) = d3175 pattern
  rw [s4961, s4964]
  rfl
theorem s4966 (pattern : Twelve) : d150 (change pattern 12 5) = d3176 pattern := by
  change (if pattern.j then d146 (change pattern 12 5) else d144 (change pattern 12 5)) = d3176 pattern
  rw [s4965, s4957]
  rfl
theorem s4967 (pattern : Twelve) : d153 (change pattern 12 5) = d3176 pattern := by
  change (if pattern.d then d150 (change pattern 12 5) else d149 (change pattern 12 5)) = d3176 pattern
  rw [s4966, s4963]
  simp only [ite_self]
theorem s4968 (pattern : Twelve) : d122 (change pattern 12 5) = d122 pattern := by
  change (if pattern.i then d4 (change pattern 12 5) else d17 (change pattern 12 5)) = d122 pattern
  rw [s4908, s4889]
  rfl
theorem s4969 (pattern : Twelve) : d131 (change pattern 12 5) = d131 pattern := by
  change (if pattern.h then d122 (change pattern 12 5) else d121 (change pattern 12 5)) = d131 pattern
  rw [s4968, s4958]
  rfl
theorem s4970 (pattern : Twelve) : d140 (change pattern 12 5) = d131 pattern := by
  change d131 (change pattern 12 5) = d131 pattern
  exact s4969 pattern
theorem s4971 (pattern : Twelve) : d141 (change pattern 12 5) = d129 pattern := by
  change d129 (change pattern 12 5) = d129 pattern
  exact s4955 pattern
theorem s4972 (pattern : Twelve) : d147 (change pattern 12 5) = d3177 pattern := by
  change (if pattern.e then d141 (change pattern 12 5) else d140 (change pattern 12 5)) = d3177 pattern
  rw [s4971, s4970]
  rfl
theorem s4973 (pattern : Twelve) : d118 (change pattern 12 5) = d118 pattern := by
  change (if pattern.k then d14 (change pattern 12 5) else d5 (change pattern 12 5)) = d118 pattern
  rw [s4911, s4910]
  rfl
theorem s4974 (pattern : Twelve) : d124 (change pattern 12 5) = d124 pattern := by
  change (if pattern.i then d118 (change pattern 12 5) else d2 (change pattern 12 5)) = d124 pattern
  rw [s4973, s4893]
  rfl
theorem s4975 (pattern : Twelve) : d117 (change pattern 12 5) = d117 pattern := by
  change (if pattern.l then d4 (change pattern 12 5) else d3 (change pattern 12 5)) = d117 pattern
  rw [s4908, s4895]
  rfl
theorem s4976 (pattern : Twelve) : d119 (change pattern 12 5) = d119 pattern := by
  change (if pattern.k then d117 (change pattern 12 5) else d3 (change pattern 12 5)) = d119 pattern
  rw [s4975, s4895]
  rfl
theorem s4977 (pattern : Twelve) : d125 (change pattern 12 5) = d125 pattern := by
  change (if pattern.i then d6 (change pattern 12 5) else d119 (change pattern 12 5)) = d125 pattern
  rw [s4902, s4976]
  rfl
theorem s4978 (pattern : Twelve) : d133 (change pattern 12 5) = d133 pattern := by
  change (if pattern.h then d125 (change pattern 12 5) else d124 (change pattern 12 5)) = d133 pattern
  rw [s4977, s4974]
  rfl
theorem s4979 (pattern : Twelve) : d142 (change pattern 12 5) = d133 pattern := by
  change d133 (change pattern 12 5) = d133 pattern
  exact s4978 pattern
theorem s4980 (pattern : Twelve) : d22 (change pattern 12 5) = d22 pattern := by
  change (if pattern.k then d6 (change pattern 12 5) else d14 (change pattern 12 5)) = d22 pattern
  rw [s4902, s4911]
  rfl
theorem s4981 (pattern : Twelve) : d127 (change pattern 12 5) = d127 pattern := by
  change (if pattern.i then d22 (change pattern 12 5) else d23 (change pattern 12 5)) = d127 pattern
  rw [s4980, s4916]
  rfl
theorem s4982 (pattern : Twelve) : d20 (change pattern 12 5) = d20 pattern := by
  change (if pattern.k then d13 (change pattern 12 5) else d12 (change pattern 12 5)) = d20 pattern
  rw [s4909, s4944]
  rfl
theorem s4983 (pattern : Twelve) : d128 (change pattern 12 5) = d128 pattern := by
  change (if pattern.i then d6 (change pattern 12 5) else d20 (change pattern 12 5)) = d128 pattern
  rw [s4902, s4982]
  rfl
theorem s4984 (pattern : Twelve) : d135 (change pattern 12 5) = d135 pattern := by
  change (if pattern.h then d128 (change pattern 12 5) else d127 (change pattern 12 5)) = d135 pattern
  rw [s4983, s4981]
  rfl
theorem s4985 (pattern : Twelve) : d143 (change pattern 12 5) = d135 pattern := by
  change d135 (change pattern 12 5) = d135 pattern
  exact s4984 pattern
theorem s4986 (pattern : Twelve) : d148 (change pattern 12 5) = d3178 pattern := by
  change (if pattern.e then d143 (change pattern 12 5) else d142 (change pattern 12 5)) = d3178 pattern
  rw [s4985, s4979]
  rfl
theorem s4987 (pattern : Twelve) : d151 (change pattern 12 5) = d3179 pattern := by
  change (if pattern.j then d148 (change pattern 12 5) else d147 (change pattern 12 5)) = d3179 pattern
  rw [s4986, s4972]
  rfl
theorem s4988 (pattern : Twelve) : d152 (change pattern 12 5) = d3180 pattern := by
  change (if pattern.j then d6 (change pattern 12 5) else d146 (change pattern 12 5)) = d3180 pattern
  rw [s4902, s4965]
  rfl
theorem s4989 (pattern : Twelve) : d154 (change pattern 12 5) = d3181 pattern := by
  change (if pattern.d then d152 (change pattern 12 5) else d151 (change pattern 12 5)) = d3181 pattern
  rw [s4988, s4987]
  rfl
theorem s4990 (pattern : Twelve) : d155 (change pattern 12 5) = d3182 pattern := by
  change (if pattern.c then d154 (change pattern 12 5) else d153 (change pattern 12 5)) = d3182 pattern
  rw [s4989, s4967]
  rfl
theorem s4991 (pattern : Twelve) : d156 (change pattern 12 5) = d3183 pattern := by
  change (if pattern.a then d155 (change pattern 12 5) else d114 (change pattern 12 5)) = d3183 pattern
  rw [s4990, s4953]
  rfl
theorem s4992 (pattern : Twelve) : d814 (change pattern 12 5) = d814 pattern := by
  change (if pattern.k then d1 (change pattern 12 5) else d7 (change pattern 12 5)) = d814 pattern
  rw [s4886, s4888]
  rfl
theorem s4993 (pattern : Twelve) : d816 (change pattern 12 5) = d816 pattern := by
  change (if pattern.i then d1 (change pattern 12 5) else d814 (change pattern 12 5)) = d816 pattern
  rw [s4886, s4992]
  rfl
theorem s4994 (pattern : Twelve) : d824 (change pattern 12 5) = d824 pattern := by
  change (if pattern.h then d816 (change pattern 12 5) else d27 (change pattern 12 5)) = d824 pattern
  rw [s4993, s4890]
  rfl
theorem s4995 (pattern : Twelve) : d838 (change pattern 12 5) = d824 pattern := by
  change d824 (change pattern 12 5) = d824 pattern
  exact s4994 pattern
theorem s4996 (pattern : Twelve) : d817 (change pattern 12 5) = d817 pattern := by
  change (if pattern.i then d25 (change pattern 12 5) else d19 (change pattern 12 5)) = d817 pattern
  rw [s4945, s4901]
  rfl
theorem s4997 (pattern : Twelve) : d825 (change pattern 12 5) = d825 pattern := by
  change (if pattern.h then d42 (change pattern 12 5) else d817 (change pattern 12 5)) = d825 pattern
  rw [s4946, s4996]
  rfl
theorem s4998 (pattern : Twelve) : d839 (change pattern 12 5) = d825 pattern := by
  change d825 (change pattern 12 5) = d825 pattern
  exact s4997 pattern
theorem s4999 (pattern : Twelve) : d853 (change pattern 12 5) = d3184 pattern := by
  change (if pattern.e then d839 (change pattern 12 5) else d838 (change pattern 12 5)) = d3184 pattern
  rw [s4998, s4995]
  rfl
theorem s5000 (pattern : Twelve) : d818 (change pattern 12 5) = d818 pattern := by
  change (if pattern.i then d6 (change pattern 12 5) else d814 (change pattern 12 5)) = d818 pattern
  rw [s4902, s4992]
  rfl
theorem s5001 (pattern : Twelve) : d826 (change pattern 12 5) = d826 pattern := by
  change (if pattern.h then d818 (change pattern 12 5) else d34 (change pattern 12 5)) = d826 pattern
  rw [s5000, s4917]
  rfl
theorem s5002 (pattern : Twelve) : d840 (change pattern 12 5) = d826 pattern := by
  change d826 (change pattern 12 5) = d826 pattern
  exact s5001 pattern
theorem s5003 (pattern : Twelve) : d841 (change pattern 12 5) = d825 pattern := by
  change d825 (change pattern 12 5) = d825 pattern
  exact s4997 pattern
theorem s5004 (pattern : Twelve) : d854 (change pattern 12 5) = d3185 pattern := by
  change (if pattern.e then d841 (change pattern 12 5) else d840 (change pattern 12 5)) = d3185 pattern
  rw [s5003, s5002]
  rfl
theorem s5005 (pattern : Twelve) : d861 (change pattern 12 5) = d3186 pattern := by
  change (if pattern.j then d854 (change pattern 12 5) else d853 (change pattern 12 5)) = d3186 pattern
  rw [s5004, s4999]
  rfl
theorem s5006 (pattern : Twelve) : d819 (change pattern 12 5) = d819 pattern := by
  change (if pattern.i then d3 (change pattern 12 5) else d814 (change pattern 12 5)) = d819 pattern
  rw [s4895, s4992]
  rfl
theorem s5007 (pattern : Twelve) : d828 (change pattern 12 5) = d828 pattern := by
  change (if pattern.h then d819 (change pattern 12 5) else d34 (change pattern 12 5)) = d828 pattern
  rw [s5006, s4917]
  rfl
theorem s5008 (pattern : Twelve) : d842 (change pattern 12 5) = d828 pattern := by
  change d828 (change pattern 12 5) = d828 pattern
  exact s5007 pattern
theorem s5009 (pattern : Twelve) : d843 (change pattern 12 5) = d825 pattern := by
  change d825 (change pattern 12 5) = d825 pattern
  exact s4997 pattern
theorem s5010 (pattern : Twelve) : d855 (change pattern 12 5) = d3187 pattern := by
  change (if pattern.e then d843 (change pattern 12 5) else d842 (change pattern 12 5)) = d3187 pattern
  rw [s5009, s5008]
  rfl
theorem s5011 (pattern : Twelve) : d815 (change pattern 12 5) = d815 pattern := by
  change (if pattern.k then d3 (change pattern 12 5) else d9 (change pattern 12 5)) = d815 pattern
  rw [s4895, s4896]
  rfl
theorem s5012 (pattern : Twelve) : d820 (change pattern 12 5) = d820 pattern := by
  change (if pattern.i then d6 (change pattern 12 5) else d815 (change pattern 12 5)) = d820 pattern
  rw [s4902, s5011]
  rfl
theorem s5013 (pattern : Twelve) : d829 (change pattern 12 5) = d829 pattern := by
  change (if pattern.h then d820 (change pattern 12 5) else d41 (change pattern 12 5)) = d829 pattern
  rw [s5012, s4942]
  rfl
theorem s5014 (pattern : Twelve) : d844 (change pattern 12 5) = d829 pattern := by
  change d829 (change pattern 12 5) = d829 pattern
  exact s5013 pattern
theorem s5015 (pattern : Twelve) : d821 (change pattern 12 5) = d821 pattern := by
  change (if pattern.i then d21 (change pattern 12 5) else d25 (change pattern 12 5)) = d821 pattern
  rw [s4912, s4945]
  rfl
theorem s5016 (pattern : Twelve) : d822 (change pattern 12 5) = d822 pattern := by
  change (if pattern.i then d6 (change pattern 12 5) else d21 (change pattern 12 5)) = d822 pattern
  rw [s4902, s4912]
  rfl
theorem s5017 (pattern : Twelve) : d831 (change pattern 12 5) = d831 pattern := by
  change (if pattern.h then d822 (change pattern 12 5) else d821 (change pattern 12 5)) = d831 pattern
  rw [s5016, s5015]
  rfl
theorem s5018 (pattern : Twelve) : d845 (change pattern 12 5) = d831 pattern := by
  change d831 (change pattern 12 5) = d831 pattern
  exact s5017 pattern
theorem s5019 (pattern : Twelve) : d856 (change pattern 12 5) = d3188 pattern := by
  change (if pattern.e then d845 (change pattern 12 5) else d844 (change pattern 12 5)) = d3188 pattern
  rw [s5018, s5014]
  rfl
theorem s5020 (pattern : Twelve) : d862 (change pattern 12 5) = d3189 pattern := by
  change (if pattern.j then d856 (change pattern 12 5) else d855 (change pattern 12 5)) = d3189 pattern
  rw [s5019, s5010]
  rfl
theorem s5021 (pattern : Twelve) : d863 (change pattern 12 5) = d3190 pattern := by
  change (if pattern.j then d6 (change pattern 12 5) else d854 (change pattern 12 5)) = d3190 pattern
  rw [s4902, s5004]
  rfl
theorem s5022 (pattern : Twelve) : d867 (change pattern 12 5) = d3191 pattern := by
  change (if pattern.d then d863 (change pattern 12 5) else d862 (change pattern 12 5)) = d3191 pattern
  rw [s5021, s5020]
  rfl
theorem s5023 (pattern : Twelve) : d869 (change pattern 12 5) = d3192 pattern := by
  change (if pattern.c then d867 (change pattern 12 5) else d861 (change pattern 12 5)) = d3192 pattern
  rw [s5022, s5005]
  rfl
theorem s5024 (pattern : Twelve) : d872 (change pattern 12 5) = d872 pattern := by
  change (if pattern.k then d8 (change pattern 12 5) else d1 (change pattern 12 5)) = d872 pattern
  rw [s4894, s4886]
  rfl
theorem s5025 (pattern : Twelve) : d874 (change pattern 12 5) = d874 pattern := by
  change (if pattern.i then d872 (change pattern 12 5) else d17 (change pattern 12 5)) = d874 pattern
  rw [s5024, s4889]
  rfl
theorem s5026 (pattern : Twelve) : d875 (change pattern 12 5) = d875 pattern := by
  change (if pattern.i then d872 (change pattern 12 5) else d814 (change pattern 12 5)) = d875 pattern
  rw [s5024, s4992]
  rfl
theorem s5027 (pattern : Twelve) : d882 (change pattern 12 5) = d882 pattern := by
  change (if pattern.h then d875 (change pattern 12 5) else d874 (change pattern 12 5)) = d882 pattern
  rw [s5026, s5025]
  rfl
theorem s5028 (pattern : Twelve) : d890 (change pattern 12 5) = d882 pattern := by
  change d882 (change pattern 12 5) = d882 pattern
  exact s5027 pattern
theorem s5029 (pattern : Twelve) : d876 (change pattern 12 5) = d876 pattern := by
  change (if pattern.i then d21 (change pattern 12 5) else d19 (change pattern 12 5)) = d876 pattern
  rw [s4912, s4901]
  rfl
theorem s5030 (pattern : Twelve) : d883 (change pattern 12 5) = d883 pattern := by
  change (if pattern.h then d42 (change pattern 12 5) else d876 (change pattern 12 5)) = d883 pattern
  rw [s4946, s5029]
  rfl
theorem s5031 (pattern : Twelve) : d891 (change pattern 12 5) = d883 pattern := by
  change d883 (change pattern 12 5) = d883 pattern
  exact s5030 pattern
theorem s5032 (pattern : Twelve) : d898 (change pattern 12 5) = d3193 pattern := by
  change (if pattern.e then d891 (change pattern 12 5) else d890 (change pattern 12 5)) = d3193 pattern
  rw [s5031, s5028]
  rfl
theorem s5033 (pattern : Twelve) : d877 (change pattern 12 5) = d877 pattern := by
  change (if pattern.i then d815 (change pattern 12 5) else d17 (change pattern 12 5)) = d877 pattern
  rw [s5011, s4889]
  rfl
theorem s5034 (pattern : Twelve) : d884 (change pattern 12 5) = d884 pattern := by
  change (if pattern.h then d818 (change pattern 12 5) else d877 (change pattern 12 5)) = d884 pattern
  rw [s5000, s5033]
  rfl
theorem s5035 (pattern : Twelve) : d892 (change pattern 12 5) = d884 pattern := by
  change d884 (change pattern 12 5) = d884 pattern
  exact s5034 pattern
theorem s5036 (pattern : Twelve) : d893 (change pattern 12 5) = d883 pattern := by
  change d883 (change pattern 12 5) = d883 pattern
  exact s5030 pattern
theorem s5037 (pattern : Twelve) : d899 (change pattern 12 5) = d3194 pattern := by
  change (if pattern.e then d893 (change pattern 12 5) else d892 (change pattern 12 5)) = d3194 pattern
  rw [s5036, s5035]
  rfl
theorem s5038 (pattern : Twelve) : d902 (change pattern 12 5) = d3195 pattern := by
  change (if pattern.j then d899 (change pattern 12 5) else d898 (change pattern 12 5)) = d3195 pattern
  rw [s5037, s5032]
  rfl
theorem s5039 (pattern : Twelve) : d878 (change pattern 12 5) = d878 pattern := by
  change (if pattern.i then d24 (change pattern 12 5) else d814 (change pattern 12 5)) = d878 pattern
  rw [s4941, s4992]
  rfl
theorem s5040 (pattern : Twelve) : d885 (change pattern 12 5) = d885 pattern := by
  change (if pattern.h then d878 (change pattern 12 5) else d877 (change pattern 12 5)) = d885 pattern
  rw [s5039, s5033]
  rfl
theorem s5041 (pattern : Twelve) : d894 (change pattern 12 5) = d885 pattern := by
  change d885 (change pattern 12 5) = d885 pattern
  exact s5040 pattern
theorem s5042 (pattern : Twelve) : d895 (change pattern 12 5) = d883 pattern := by
  change d883 (change pattern 12 5) = d883 pattern
  exact s5030 pattern
theorem s5043 (pattern : Twelve) : d900 (change pattern 12 5) = d3196 pattern := by
  change (if pattern.e then d895 (change pattern 12 5) else d894 (change pattern 12 5)) = d3196 pattern
  rw [s5042, s5041]
  rfl
theorem s5044 (pattern : Twelve) : d873 (change pattern 12 5) = d873 pattern := by
  change (if pattern.k then d15 (change pattern 12 5) else d117 (change pattern 12 5)) = d873 pattern
  rw [s4940, s4975]
  rfl
theorem s5045 (pattern : Twelve) : d880 (change pattern 12 5) = d880 pattern := by
  change (if pattern.i then d6 (change pattern 12 5) else d873 (change pattern 12 5)) = d880 pattern
  rw [s4902, s5044]
  rfl
theorem s5046 (pattern : Twelve) : d887 (change pattern 12 5) = d887 pattern := by
  change (if pattern.h then d880 (change pattern 12 5) else d127 (change pattern 12 5)) = d887 pattern
  rw [s5045, s4981]
  rfl
theorem s5047 (pattern : Twelve) : d896 (change pattern 12 5) = d887 pattern := by
  change d887 (change pattern 12 5) = d887 pattern
  exact s5046 pattern
theorem s5048 (pattern : Twelve) : d889 (change pattern 12 5) = d889 pattern := by
  change (if pattern.h then d6 (change pattern 12 5) else d42 (change pattern 12 5)) = d889 pattern
  rw [s4902, s4946]
  rfl
theorem s5049 (pattern : Twelve) : d897 (change pattern 12 5) = d889 pattern := by
  change d889 (change pattern 12 5) = d889 pattern
  exact s5048 pattern
theorem s5050 (pattern : Twelve) : d901 (change pattern 12 5) = d3197 pattern := by
  change (if pattern.e then d897 (change pattern 12 5) else d896 (change pattern 12 5)) = d3197 pattern
  rw [s5049, s5047]
  rfl
theorem s5051 (pattern : Twelve) : d903 (change pattern 12 5) = d3198 pattern := by
  change (if pattern.j then d901 (change pattern 12 5) else d900 (change pattern 12 5)) = d3198 pattern
  rw [s5050, s5043]
  rfl
theorem s5052 (pattern : Twelve) : d904 (change pattern 12 5) = d3199 pattern := by
  change (if pattern.j then d6 (change pattern 12 5) else d899 (change pattern 12 5)) = d3199 pattern
  rw [s4902, s5037]
  rfl
theorem s5053 (pattern : Twelve) : d905 (change pattern 12 5) = d3200 pattern := by
  change (if pattern.d then d904 (change pattern 12 5) else d903 (change pattern 12 5)) = d3200 pattern
  rw [s5052, s5051]
  rfl
theorem s5054 (pattern : Twelve) : d906 (change pattern 12 5) = d3201 pattern := by
  change (if pattern.c then d905 (change pattern 12 5) else d902 (change pattern 12 5)) = d3201 pattern
  rw [s5053, s5038]
  rfl
theorem s5055 (pattern : Twelve) : d907 (change pattern 12 5) = d3202 pattern := by
  change (if pattern.a then d906 (change pattern 12 5) else d869 (change pattern 12 5)) = d3202 pattern
  rw [s5054, s5023]
  rfl
theorem s5056 (pattern : Twelve) : d1275 (change pattern 12 5) = d1275 pattern := by
  change (if pattern.k then d8 (change pattern 12 5) else d7 (change pattern 12 5)) = d1275 pattern
  rw [s4894, s4888]
  rfl
theorem s5057 (pattern : Twelve) : d1278 (change pattern 12 5) = d1278 pattern := by
  change (if pattern.i then d872 (change pattern 12 5) else d1275 (change pattern 12 5)) = d1278 pattern
  rw [s5024, s5056]
  rfl
theorem s5058 (pattern : Twelve) : d1284 (change pattern 12 5) = d1284 pattern := by
  change (if pattern.h then d872 (change pattern 12 5) else d1278 (change pattern 12 5)) = d1284 pattern
  rw [s5024, s5057]
  rfl
theorem s5059 (pattern : Twelve) : d1293 (change pattern 12 5) = d1284 pattern := by
  change d1284 (change pattern 12 5) = d1284 pattern
  exact s5058 pattern
theorem s5060 (pattern : Twelve) : d1294 (change pattern 12 5) = d6 pattern := by
  change d6 (change pattern 12 5) = d6 pattern
  exact s4902 pattern
theorem s5061 (pattern : Twelve) : d1305 (change pattern 12 5) = d3203 pattern := by
  change (if pattern.e then d1294 (change pattern 12 5) else d1293 (change pattern 12 5)) = d3203 pattern
  rw [s5060, s5059]
  rfl
theorem s5062 (pattern : Twelve) : d1276 (change pattern 12 5) = d1276 pattern := by
  change (if pattern.k then d117 (change pattern 12 5) else d9 (change pattern 12 5)) = d1276 pattern
  rw [s4975, s4896]
  rfl
theorem s5063 (pattern : Twelve) : d1279 (change pattern 12 5) = d1279 pattern := by
  change (if pattern.i then d1276 (change pattern 12 5) else d1275 (change pattern 12 5)) = d1279 pattern
  rw [s5062, s5056]
  rfl
theorem s5064 (pattern : Twelve) : d1280 (change pattern 12 5) = d1280 pattern := by
  change (if pattern.i then d6 (change pattern 12 5) else d872 (change pattern 12 5)) = d1280 pattern
  rw [s4902, s5024]
  rfl
theorem s5065 (pattern : Twelve) : d1285 (change pattern 12 5) = d1285 pattern := by
  change (if pattern.h then d1280 (change pattern 12 5) else d1279 (change pattern 12 5)) = d1285 pattern
  rw [s5064, s5063]
  rfl
theorem s5066 (pattern : Twelve) : d1295 (change pattern 12 5) = d1285 pattern := by
  change d1285 (change pattern 12 5) = d1285 pattern
  exact s5065 pattern
theorem s5067 (pattern : Twelve) : d1296 (change pattern 12 5) = d6 pattern := by
  change d6 (change pattern 12 5) = d6 pattern
  exact s4902 pattern
theorem s5068 (pattern : Twelve) : d1306 (change pattern 12 5) = d3204 pattern := by
  change (if pattern.e then d1296 (change pattern 12 5) else d1295 (change pattern 12 5)) = d3204 pattern
  rw [s5067, s5066]
  rfl
theorem s5069 (pattern : Twelve) : d1313 (change pattern 12 5) = d3205 pattern := by
  change (if pattern.j then d1306 (change pattern 12 5) else d1305 (change pattern 12 5)) = d3205 pattern
  rw [s5068, s5061]
  rfl
theorem s5070 (pattern : Twelve) : d1281 (change pattern 12 5) = d1281 pattern := by
  change (if pattern.i then d119 (change pattern 12 5) else d872 (change pattern 12 5)) = d1281 pattern
  rw [s4976, s5024]
  rfl
theorem s5071 (pattern : Twelve) : d1287 (change pattern 12 5) = d1287 pattern := by
  change (if pattern.h then d1281 (change pattern 12 5) else d1279 (change pattern 12 5)) = d1287 pattern
  rw [s5070, s5063]
  rfl
theorem s5072 (pattern : Twelve) : d1297 (change pattern 12 5) = d1287 pattern := by
  change d1287 (change pattern 12 5) = d1287 pattern
  exact s5071 pattern
theorem s5073 (pattern : Twelve) : d1298 (change pattern 12 5) = d6 pattern := by
  change d6 (change pattern 12 5) = d6 pattern
  exact s4902 pattern
theorem s5074 (pattern : Twelve) : d1307 (change pattern 12 5) = d3206 pattern := by
  change (if pattern.e then d1298 (change pattern 12 5) else d1297 (change pattern 12 5)) = d3206 pattern
  rw [s5073, s5072]
  rfl
theorem s5075 (pattern : Twelve) : d1277 (change pattern 12 5) = d1277 pattern := by
  change (if pattern.k then d14 (change pattern 12 5) else d15 (change pattern 12 5)) = d1277 pattern
  rw [s4911, s4940]
  rfl
theorem s5076 (pattern : Twelve) : d1282 (change pattern 12 5) = d1282 pattern := by
  change (if pattern.i then d1277 (change pattern 12 5) else d1276 (change pattern 12 5)) = d1282 pattern
  rw [s5075, s5062]
  rfl
theorem s5077 (pattern : Twelve) : d1288 (change pattern 12 5) = d1288 pattern := by
  change (if pattern.h then d125 (change pattern 12 5) else d1282 (change pattern 12 5)) = d1288 pattern
  rw [s4977, s5076]
  rfl
theorem s5078 (pattern : Twelve) : d1299 (change pattern 12 5) = d1288 pattern := by
  change d1288 (change pattern 12 5) = d1288 pattern
  exact s5077 pattern
theorem s5079 (pattern : Twelve) : d1300 (change pattern 12 5) = d6 pattern := by
  change d6 (change pattern 12 5) = d6 pattern
  exact s4902 pattern
theorem s5080 (pattern : Twelve) : d1308 (change pattern 12 5) = d3207 pattern := by
  change (if pattern.e then d1300 (change pattern 12 5) else d1299 (change pattern 12 5)) = d3207 pattern
  rw [s5079, s5078]
  rfl
theorem s5081 (pattern : Twelve) : d1314 (change pattern 12 5) = d3208 pattern := by
  change (if pattern.j then d1308 (change pattern 12 5) else d1307 (change pattern 12 5)) = d3208 pattern
  rw [s5080, s5074]
  rfl
theorem s5082 (pattern : Twelve) : d1315 (change pattern 12 5) = d3209 pattern := by
  change (if pattern.j then d6 (change pattern 12 5) else d1306 (change pattern 12 5)) = d3209 pattern
  rw [s4902, s5068]
  rfl
theorem s5083 (pattern : Twelve) : d1319 (change pattern 12 5) = d3210 pattern := by
  change (if pattern.d then d1315 (change pattern 12 5) else d1314 (change pattern 12 5)) = d3210 pattern
  rw [s5082, s5081]
  rfl
theorem s5084 (pattern : Twelve) : d1321 (change pattern 12 5) = d3211 pattern := by
  change (if pattern.c then d1319 (change pattern 12 5) else d1313 (change pattern 12 5)) = d3211 pattern
  rw [s5083, s5069]
  rfl
theorem s5085 (pattern : Twelve) : d1324 (change pattern 12 5) = d1324 pattern := by
  change (if pattern.k then d16 (change pattern 12 5) else d11 (change pattern 12 5)) = d1324 pattern
  rw [s4943, s4900]
  rfl
theorem s5086 (pattern : Twelve) : d1325 (change pattern 12 5) = d1325 pattern := by
  change (if pattern.i then d1324 (change pattern 12 5) else d1275 (change pattern 12 5)) = d1325 pattern
  rw [s5085, s5056]
  rfl
theorem s5087 (pattern : Twelve) : d1326 (change pattern 12 5) = d1326 pattern := by
  change (if pattern.i then d1324 (change pattern 12 5) else d872 (change pattern 12 5)) = d1326 pattern
  rw [s5085, s5024]
  rfl
theorem s5088 (pattern : Twelve) : d1333 (change pattern 12 5) = d1333 pattern := by
  change (if pattern.h then d1326 (change pattern 12 5) else d1325 (change pattern 12 5)) = d1333 pattern
  rw [s5087, s5086]
  rfl
theorem s5089 (pattern : Twelve) : d1339 (change pattern 12 5) = d1333 pattern := by
  change d1333 (change pattern 12 5) = d1333 pattern
  exact s5088 pattern
theorem s5090 (pattern : Twelve) : d1345 (change pattern 12 5) = d3212 pattern := by
  change (if pattern.e then d1294 (change pattern 12 5) else d1339 (change pattern 12 5)) = d3212 pattern
  rw [s5060, s5089]
  rfl
theorem s5091 (pattern : Twelve) : d1327 (change pattern 12 5) = d1327 pattern := by
  change (if pattern.i then d119 (change pattern 12 5) else d1275 (change pattern 12 5)) = d1327 pattern
  rw [s4976, s5056]
  rfl
theorem s5092 (pattern : Twelve) : d1334 (change pattern 12 5) = d1334 pattern := by
  change (if pattern.h then d1280 (change pattern 12 5) else d1327 (change pattern 12 5)) = d1334 pattern
  rw [s5064, s5091]
  rfl
theorem s5093 (pattern : Twelve) : d1340 (change pattern 12 5) = d1334 pattern := by
  change d1334 (change pattern 12 5) = d1334 pattern
  exact s5092 pattern
theorem s5094 (pattern : Twelve) : d1346 (change pattern 12 5) = d3213 pattern := by
  change (if pattern.e then d1296 (change pattern 12 5) else d1340 (change pattern 12 5)) = d3213 pattern
  rw [s5067, s5093]
  rfl
theorem s5095 (pattern : Twelve) : d1349 (change pattern 12 5) = d3214 pattern := by
  change (if pattern.j then d1346 (change pattern 12 5) else d1345 (change pattern 12 5)) = d3214 pattern
  rw [s5094, s5090]
  rfl
theorem s5096 (pattern : Twelve) : d1328 (change pattern 12 5) = d1328 pattern := by
  change (if pattern.i then d1277 (change pattern 12 5) else d872 (change pattern 12 5)) = d1328 pattern
  rw [s5075, s5024]
  rfl
theorem s5097 (pattern : Twelve) : d1335 (change pattern 12 5) = d1335 pattern := by
  change (if pattern.h then d1328 (change pattern 12 5) else d1327 (change pattern 12 5)) = d1335 pattern
  rw [s5096, s5091]
  rfl
theorem s5098 (pattern : Twelve) : d1341 (change pattern 12 5) = d1335 pattern := by
  change d1335 (change pattern 12 5) = d1335 pattern
  exact s5097 pattern
theorem s5099 (pattern : Twelve) : d1342 (change pattern 12 5) = d6 pattern := by
  change d6 (change pattern 12 5) = d6 pattern
  exact s4902 pattern
end NetHack.Sokoban21.Diagram
