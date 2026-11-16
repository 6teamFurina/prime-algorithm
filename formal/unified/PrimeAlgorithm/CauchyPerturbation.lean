import PrimeAlgorithm.CauchyKernel

/-! Quantizing the poles and residues does not destroy the Cauchy error bound.
The premises are explicit local approximation certificates, not a bound on the
final prime sum. -/

noncomputable section
namespace PrimeAlgorithm.Cauchy
open Finset

theorem quotient_perturbation (u u' v v' : ℂ) (H δ : ℝ)
    (hH : 0 ≤ H) (hδ : 0 ≤ δ) (hu : ‖u‖ ≤ H)
    (hdu : ‖u' - u‖ ≤ δ) (hdv : ‖v' - v‖ ≤ δ)
    (hv : (1 / 4 : ℝ) ≤ ‖v‖) (hv' : (1 / 8 : ℝ) ≤ ‖v'‖) :
    ‖u' / v' - u / v‖ ≤ (8 + 32 * H) * δ := by
  have hv0 : v ≠ 0 := by intro h; norm_num [h] at hv
  have hv'0 : v' ≠ 0 := by intro h; norm_num [h] at hv'
  have hid : u' / v' - u / v = (u' - u) / v' + u * (v - v') / (v' * v) := by
    field_simp
    ring
  rw [hid]
  have h1 : ‖(u' - u) / v'‖ ≤ 8 * δ := by
    rw [norm_div]
    calc
      _ ≤ δ / (1 / 8 : ℝ) := div_le_div₀ hδ hdu (by norm_num) hv'
      _ = _ := by ring
  have h2 : ‖u * (v - v') / (v' * v)‖ ≤ 32 * H * δ := by
    rw [norm_div, norm_mul, norm_mul, norm_sub_rev v v']
    have hd : (1 / 32 : ℝ) ≤ ‖v'‖ * ‖v‖ := by nlinarith
    calc
      _ ≤ (H * δ) / (1 / 32 : ℝ) :=
        div_le_div₀ (mul_nonneg hH hδ)
          (mul_le_mul hu hdv (norm_nonneg _) hH) (by norm_num) hd
      _ = _ := by ring
  have ht := norm_add_le ((u' - u) / v') (u * (v - v') / (v' * v))
  linarith

theorem perturbed_kernel_error (θ : ℝ) {y : ℝ} (hy : y ∈ Set.Icc 1 2)
    (u u' z : ℂ) (H δ : ℝ) (hH : 0 ≤ H) (hδ : 0 ≤ δ)
    (hsmall : δ ≤ (1 / 8 : ℝ)) (hu : ‖u‖ ≤ H)
    (hdu : ‖u' - u‖ ≤ δ) (hdz : ‖z - node θ‖ ≤ δ) :
    ‖u' / (z - y) - u / (node θ - y)‖ ≤ (8 + 32 * H) * δ := by
  apply quotient_perturbation u u' (node θ - y) (z - y) H δ hH hδ hu hdu
  · simpa only [sub_sub_sub_cancel_right] using hdz
  · exact node_separation θ hy
  · exact perturbed_separation θ hy (hdz.trans hsmall)

/-- The division by M cancels the M local perturbation errors. -/
theorem average_error (M : ℕ) (hM : 0 < M) (f g : ℕ → ℂ) (E : ℝ)
    (h : ∀ j ∈ range M, ‖f j - g j‖ ≤ E) :
    ‖((∑ j ∈ range M, f j) / (M : ℂ)) -
      ((∑ j ∈ range M, g j) / (M : ℂ))‖ ≤ E := by
  rw [← sub_div, ← sum_sub_distrib, norm_div, Complex.norm_natCast]
  have hb : ‖∑ j ∈ range M, (f j - g j)‖ ≤ (M : ℝ) * E := by
    calc
      _ ≤ ∑ _j ∈ range M, E := norm_sum_le_of_le _ h
      _ = _ := by simp
  exact (div_le_iff₀ (by exact_mod_cast hM)).2 (by simpa [mul_comm] using hb)

end PrimeAlgorithm.Cauchy
