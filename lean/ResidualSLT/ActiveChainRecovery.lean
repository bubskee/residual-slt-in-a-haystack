module
public import ResidualSLT.SmallActiveGlobalLaplace

/-! Exact recovery of arbitrarily long normalized residual compositions. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial Finset

/-- The divided difference of equal-leading-term polynomials has its expected degree. -/
theorem geometric_factor_natDegree (H G : ℝ[X]) (hH : H≠0) (hG : G≠0)
    (hd : G.natDegree=H.natDegree) (hc : G.leadingCoeff=H.leadingCoeff)
    (r : ℕ) (hr : 0<r) :
    (∑ i ∈ range r,H^i*G^(r-1-i)).natDegree=(r-1)*H.natDegree := by
  have ht (i : ℕ) (hi : i∈range r) : (H^i*G^(r-1-i)).natDegree=(r-1)*H.natDegree := by
    rw [natDegree_mul (pow_ne_zero _ hH) (pow_ne_zero _ hG),natDegree_pow,natDegree_pow,hd]
    have he : i+(r-1-i)=r-1 := by have hh := mem_range.mp hi; omega
    nlinarith
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact natDegree_sum_le_of_forall_le _ _ (fun i hi => (ht i hi).le)
  · rw [finsetSum_coeff]
    have he (i : ℕ) (hi : i∈range r) : (H^i*G^(r-1-i)).coeff ((r-1)*H.natDegree)=H.leadingCoeff^(r-1) := by
      rw [← ht i hi,coeff_natDegree,leadingCoeff_mul,leadingCoeff_pow,leadingCoeff_pow,hc,← pow_add]
      congr 1
      have hh := mem_range.mp hi
      omega
    simp_rw [sum_congr rfl he]
    simp only [sum_const,card_range,nsmul_eq_mul]
    exact mul_ne_zero (by exact_mod_cast hr.ne') (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hH))

/-- An outer residual block and its normalized inner polynomial are uniquely determined.
The proof uses degree and leading coefficients, with no genericity or sign assumption. -/
theorem normalized_residual_append_injective (r : ℕ) (hr : 2≤r)
    (H G : ℝ[X]) (hH0 : H.coeff 0=0) (hG0 : G.coeff 0=0)
    (hH1 : H.coeff 1=1) (hG1 : G.coeff 1=1) (c d : ℝ) (hc : c≠0) (hd : d≠0)
    (he : H+C c*H^r=G+C d*G^r) : H=G ∧ c=d := by
  have hH : H≠0 := by
    intro hz
    rw [hz] at hH1
    norm_num at hH1
  have hG : G≠0 := by
    intro hz
    rw [hz] at hG1
    norm_num at hG1
  have hpH : 0<H.natDegree := by
    by_contra hh
    have hz := eq_C_of_natDegree_eq_zero (show H.natDegree=0 by omega)
    rw [hz] at hH1
    norm_num at hH1
  have hpG : 0<G.natDegree := by
    by_contra hh
    have hz := eq_C_of_natDegree_eq_zero (show G.natDegree=0 by omega)
    rw [hz] at hG1
    norm_num at hG1
  have hedeg := congrArg natDegree he
  rw [append_active_natDegree r hr H hpH c hc,append_active_natDegree r hr G hpG d hd] at hedeg
  have hdeg : G.natDegree=H.natDegree := by nlinarith
  have hlead : c*H.leadingCoeff^r=d*G.leadingCoeff^r := by
    have hh := congrArg (fun P : ℝ[X] => P.coeff (r*H.natDegree)) he
    have hlowH : H.coeff (r*H.natDegree)=0 := coeff_eq_zero_of_natDegree_lt (by nlinarith)
    have hlowG : G.coeff (r*H.natDegree)=0 := coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; nlinarith)
    have hpowH : (H^r).coeff (r*H.natDegree)=H.leadingCoeff^r := by
      rw [← natDegree_pow,coeff_natDegree,leadingCoeff_pow]
    have hpowG : (G^r).coeff (r*H.natDegree)=G.leadingCoeff^r := by
      rw [← hdeg,← natDegree_pow,coeff_natDegree,leadingCoeff_pow]
    simpa only [coeff_add,coeff_C_mul,hlowH,hlowG,hpowH,hpowG,zero_add] using hh
  let a := H.leadingCoeff/G.leadingCoeff
  have ha : a≠0 := div_ne_zero (leadingCoeff_ne_zero.mpr hH) (leadingCoeff_ne_zero.mpr hG)
  have hd' : d=c*a^r := by
    dsimp [a]
    rw [div_pow,← mul_div_assoc]
    exact (eq_div_iff (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hG))).mpr hlead.symm
  let U := C a*G
  have hU : U≠0 := mul_ne_zero (by simpa using ha) hG
  have hUd : U.natDegree=H.natDegree := by rw [natDegree_C_mul ha,hdeg]
  have hUc : U.leadingCoeff=H.leadingCoeff := by
    simp only [U,leadingCoeff_mul,leadingCoeff_C,a]
    exact div_mul_cancel₀ _ (leadingCoeff_ne_zero.mpr hG)
  have hEq : C c*(H^r-U^r)=G-H := by
    have hh : C d*G^r=C c*U^r := by simp only [U,hd',map_mul,map_pow,mul_pow]; ring
    rw [hh] at he
    linear_combination he
  have hHU : H=U := by
    by_contra hne
    have hsub : H-U≠0 := sub_ne_zero.mpr hne
    have hsub0 : (H-U).coeff 0=0 := by simp [U,hH0,hG0]
    have hsubpos : 0<(H-U).natDegree := by
      by_contra hh
      have hz := eq_C_of_natDegree_eq_zero (show (H-U).natDegree=0 by omega)
      rw [hsub0,map_zero] at hz
      exact hsub hz
    let S := ∑ i ∈ range r,H^i*U^(r-1-i)
    have hSd : S.natDegree=(r-1)*H.natDegree := geometric_factor_natDegree H U hH hU hUd hUc r (by omega)
    have hS : S≠0 := by intro hz; simp only [hz,natDegree_zero] at hSd; nlinarith [show 1≤r-1 by omega]
    have hprod : C c*(S*(H-U))=G-H := by rw [geom_sum₂_mul]; exact hEq
    have hpd := congrArg natDegree hprod
    rw [natDegree_C_mul hc,natDegree_mul hS hsub,hSd] at hpd
    have hh := natDegree_sub_le G H
    rw [hdeg,max_self,← hpd] at hh
    have hrr : 1≤r-1 := by omega
    nlinarith
  have ha1 : a=1 := by
    have hh := congrArg (fun P : ℝ[X] => P.coeff 1) hHU
    simpa [U,hH1,hG1] using hh.symm
  exact ⟨by simpa [U,ha1] using hHU,by simpa [ha1] using hd'.symm⟩

end ResidualSLT
