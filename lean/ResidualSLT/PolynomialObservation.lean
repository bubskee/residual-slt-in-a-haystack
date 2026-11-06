module
public import ResidualSLT.OneActiveDirections
public import Mathlib.Algebra.Polynomial.Roots

/-! Exact finite observations preserve independence below the interpolation degree. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial Finset Set

theorem polynomial_observation_independent {ι κ : Type*} [Fintype ι] [Fintype κ]
    (v : ι → ℝ[X]) (hv : LinearIndependent ℝ v) (x : κ → ℝ)
    (hx : Function.Injective x) (hd : ∀ i, (v i).natDegree < Fintype.card κ) :
    LinearIndependent ℝ (fun i k => (v i).eval (x k)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  have hp : (∑ i, c i • v i) = 0 := by
    by_cases hz : (∑ i, c i • v i) = 0
    · exact hz
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hx
    · intro k
      have hh := congrFun hc k
      simpa [Polynomial.eval_finsetSum,Polynomial.eval_smul] using hh
    · have hm : (∑ i, c i • v i) ∈ degreeLT ℝ (Fintype.card κ) := by
        apply Submodule.sum_mem
        intro i _
        apply Submodule.smul_mem
        rw [mem_degreeLT]
        exact degree_le_natDegree.trans_lt (by exact_mod_cast hd i)
      exact (natDegree_lt_iff_degree_lt hz).mpr (mem_degreeLT.mp hm)
  exact Fintype.linearIndependent_iff.mp hv c hp

end ResidualSLT
