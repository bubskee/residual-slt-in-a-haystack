module
public import ResidualSLT.ArrangementCertificate
public import Mathlib.Algebra.Polynomial.Coeff

/-! Ordered one- and two-active polynomial targets and exact coefficient recovery. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial Finset

@[expose] def twoActiveTarget (r : ℕ) (c d : ℝ) : ℝ[X] :=
  (activeTarget r d).comp (activeTarget r c)

@[expose] def twoActiveEffective (c d : ℝ) (i : ℕ) : ℝ := if i=0 then c else d

theorem network_two_active (r : ℕ) (c d : ℝ) :
    network r (twoActiveEffective c d) 2 = twoActiveTarget r c d := by
  simp [network,twoActiveEffective,twoActiveTarget,activeTarget]

theorem twoActiveTarget_natDegree (r : ℕ) (hr : 2 ≤ r) (c d : ℝ) (hc : c ≠ 0) (hd : d ≠ 0) :
    (twoActiveTarget r c d).natDegree = r^2 := by
  rw [twoActiveTarget,natDegree_comp,activeTarget_natDegree r hr d hd,activeTarget_natDegree r hr c hc,pow_two]

theorem activeTarget_injective (r : ℕ) (hr : 2 ≤ r) : Function.Injective (activeTarget r) := by
  intro c d he
  have hh := congrArg (fun p : ℝ[X] => p.coeff r) he
  simpa [activeTarget,coeff_X,show 1 ≠ r by omega] using hh

theorem coeff_one_add_C_mul_X_pow (r j : ℕ) (c : ℝ) :
    ((1+C c*X)^r).coeff j = (r.choose j:ℝ)*c^j := by
  have he : (1+C c*X)^r = ((1+X)^r).comp (C c*X) := by simp
  rw [he,comp_C_mul_X_coeff,coeff_one_add_X_pow]

theorem two_active_graded_coefficients (r : ℕ) (c d : ℝ) :
    (graded r (twoActiveEffective c d) 2).coeff 1 = c+d ∧
    (graded r (twoActiveEffective c d) 2).coeff 2 = (r:ℝ)*c*d ∧
    (graded r (twoActiveEffective c d) 2).coeff 3 = (r.choose 2:ℝ)*c^2*d := by
  have he : graded r (twoActiveEffective c d) 2 = 1+C c*X+C d*X*(1+C c*X)^r := by
    simp [graded,twoActiveEffective]
  rw [he]
  simp only [coeff_add,mul_assoc,coeff_C_mul,coeff_X_mul,coeff_one_add_C_mul_X_pow]
  simp [coeff_one,coeff_X,mul_comm,mul_left_comm,mul_assoc]

/-- The first three residual coefficients recover the ordered pair, including equal or
opposite nonzero active coefficients and quadratic degree. -/
theorem twoActiveTarget_injective (r : ℕ) (hr : 2 ≤ r) (c d u v : ℝ)
    (hc : c ≠ 0) (hd : d ≠ 0)
    (he : twoActiveTarget r u v = twoActiveTarget r c d) : u=c ∧ v=d := by
  have hcoef (j : ℕ) : (graded r (twoActiveEffective u v) 2).coeff j =
      (graded r (twoActiveEffective c d) 2).coeff j := by
    rw [← network_coeff_graded r hr,← network_coeff_graded r hr,network_two_active,network_two_active,he]
  obtain ⟨hc1,hc2,hc3⟩ := two_active_graded_coefficients r c d
  obtain ⟨hu1,hu2,hu3⟩ := two_active_graded_coefficients r u v
  have h1 : u+v=c+d := by rw [← hu1,← hc1]; exact hcoef 1
  have h2 : u*v=c*d := by
    have hh := hcoef 2
    rw [hc2,hu2] at hh
    have hr0 : (r:ℝ) ≠ 0 := by positivity
    exact mul_left_cancel₀ hr0 (by simpa [mul_assoc] using hh)
  have h3 : u^2*v=c^2*d := by
    have hh := hcoef 3
    rw [hc3,hu3] at hh
    have hb : (r.choose 2:ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hr).ne'
    exact mul_left_cancel₀ hb (by simpa [mul_assoc] using hh)
  have hu : u=c := by
    apply mul_right_cancel₀ (mul_ne_zero hc hd)
    calc
      u*(c*d) = u*(u*v) := by rw [h2]
      _ = c*(c*d) := by nlinarith [h3]
  exact ⟨hu,by linarith⟩

end ResidualSLT
