module
public import ResidualSLT.PolynomialNetworks

/-! Exact degree counts and the full polynomial identity fiber over any integral domain. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial Finset
variable {R : Type*} [CommRing R]
local instance : DecidableEq R := Classical.decEq R

/-- An active block has nonzero effective coefficient. -/
@[expose] def activeCount (u : ℕ → R) (n : ℕ) : ℕ := by
  classical
  exact ((range n).filter (fun i => u i ≠ 0)).card

@[simp] theorem activeCount_zero (u : ℕ → R) : activeCount u 0 = 0 := by
  classical
  simp [activeCount]

theorem activeCount_succ (u : ℕ → R) (n : ℕ) :
    activeCount u (n + 1) = activeCount u n + if u n = 0 then 0 else 1 := by
  classical
  simp [activeCount, range_add_one, filter_insert]
  split_ifs <;> simp_all

variable [IsDomain R]

/-- Nonzero residual blocks multiply polynomial degree by `r`; zero blocks do nothing. -/
theorem network_natDegree (r : ℕ) (hr : 2 ≤ r) (u : ℕ → R) (n : ℕ) :
    (network r u n).natDegree = r ^ activeCount u n := by
  classical
  induction n with
  | zero => simp [network]
  | succ n ih =>
    rw [activeCount_succ]
    by_cases hu : u n = 0
    · simp [network, hu, ih]
    · rw [ite_eq_right hu, pow_succ]
      have hdeg : (network r u n).natDegree < (C (u n) * network r u n ^ r).natDegree := by
        rw [natDegree_C_mul hu, natDegree_pow, ih]
        have hp : 0 < r ^ activeCount u n := pow_pos (by omega) _
        nlinarith
      rw [network, natDegree_add_eq_right_of_natDegree_lt hdeg, natDegree_C_mul hu,
        natDegree_pow, ih]
      exact Nat.mul_comm _ _

omit [IsDomain R] in
theorem activeCount_le (u : ℕ → R) (n : ℕ) : activeCount u n ≤ n := by
  classical
  exact (card_filter_le ..).trans_eq (card_range n)

/-- The familiar maximal degree bound, valid without any genericity assumption. -/
theorem network_natDegree_le (r : ℕ) (hr : 2 ≤ r) (u : ℕ → R) (n : ℕ) :
    (network r u n).natDegree ≤ r ^ n := by
  rw [network_natDegree r hr]
  exact Nat.pow_le_pow_right (by omega) (activeCount_le u n)

/-- The entire identity fiber, not just the vanishing locus of its first two coefficients. -/
theorem network_eq_X_iff (r : ℕ) (hr : 2 ≤ r) (u : ℕ → R) (n : ℕ) :
    network r u n = X ↔ ∀ i < n, u i = 0 := by
  classical
  constructor
  · intro h
    have hc : activeCount u n = 0 := by
      apply Nat.pow_right_injective hr
      simpa [h] using (network_natDegree r hr u n).symm
    intro i hi
    by_contra hui
    have : i ∈ (range n).filter (fun j => u j ≠ 0) := by simp [hi, hui]
    have hempty : (range n).filter (fun j => u j ≠ 0) = ∅ := card_eq_zero.mp hc
    simp [hempty] at this
  · intro h
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [network_succ_of_zero r n u (h n (by omega))]
      exact ih (fun i hi => h i (by omega))

/-- Raw-weight identity fiber, over `ℝ`, `ℂ`, or any integral domain. -/
theorem raw_network_eq_X_iff (r : ℕ) (hr : 2 ≤ r) (w : ℕ → R) (n : ℕ) :
    network r (fun i => w i ^ r) n = X ↔ ∀ i < n, w i = 0 := by
  rw [network_eq_X_iff r hr]
  simp [pow_eq_zero_iff (by omega : r ≠ 0)]
end ResidualSLT
