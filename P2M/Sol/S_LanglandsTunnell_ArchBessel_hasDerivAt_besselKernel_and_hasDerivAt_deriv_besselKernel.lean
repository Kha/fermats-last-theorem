import Mathlib.Analysis.MellinTransform
import Definitions.Def_LanglandsTunnell_ArchBessel
import Theorems.Thm_LanglandsTunnell_ArchBessel_hasDerivAt_besselKernel
import Theorems.Thm_LanglandsTunnell_ArchBessel_mul_besselKernel_eq_mul_sub
import Mathlib
import P2M.Util
namespace P2MW.S_LanglandsTunnell_ArchBessel_hasDerivAt_besselKernel_and_hasDerivAt_deriv_besselKernel

set_option autoImplicit false

open LanglandsTunnell.ArchBessel

theorem solution
    (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => besselKernel ν x) (-besselKernel (ν + 1) x + ν / (x : ℂ) * besselKernel ν x) x ∧
      HasDerivAt (deriv fun x : ℝ => besselKernel ν x)
        ((1 + ν ^ 2 / (x : ℂ) ^ 2) * besselKernel ν x - (deriv (fun x : ℝ => besselKernel ν x) x) / (x : ℂ)) x := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'

  have clause1 : ∀ (μ : ℂ) (y : ℝ), 0 < y →
      HasDerivAt (fun x : ℝ => besselKernel μ x) (-besselKernel (μ + 1) y + μ / (y : ℂ) * besselKernel μ y) y := by
    intro μ y hy
    have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
    have h1 := LanglandsTunnell.ArchBessel.hasDerivAt_besselKernel μ y hy
    have h2 := LanglandsTunnell.ArchBessel.mul_besselKernel_eq_mul_sub μ y hy
    refine h1.congr_deriv ?_
    have h3 : μ / (y : ℂ) * besselKernel μ y = (besselKernel (μ + 1) y - besselKernel (μ - 1) y) / 2 := by
      rw [div_mul_eq_mul_div, div_eq_iff hy0, h2]; ring
    rw [h3]; ring
  refine ⟨clause1 ν x hx, ?_⟩
  set g : ℝ → ℂ := fun y => -besselKernel (ν + 1) y + ν / (y : ℂ) * besselKernel ν y with hg
  have hev : (deriv fun x : ℝ => besselKernel ν x) =ᶠ[nhds x] g := by
    have hmem : Set.Ioi (0 : ℝ) ∈ nhds x := isOpen_Ioi.mem_nhds hx
    refine Filter.eventually_of_mem hmem fun y hy => ?_
    exact (clause1 ν y hy).deriv
  have hdx : deriv (fun x : ℝ => besselKernel ν x) x = -besselKernel (ν + 1) x + ν / (x : ℂ) * besselKernel ν x :=
    (clause1 ν x hx).deriv
  have hA : HasDerivAt (fun y : ℝ => besselKernel (ν + 1) y)
      (-besselKernel (ν + 1 + 1) x + (ν + 1) / (x : ℂ) * besselKernel (ν + 1) x) x := clause1 (ν + 1) x hx
  have hB : HasDerivAt (fun y : ℝ => besselKernel ν y) (-besselKernel (ν + 1) x + ν / (x : ℂ) * besselKernel ν x) x :=
    clause1 ν x hx
  have hinv : HasDerivAt (fun y : ℝ => ((y : ℂ))⁻¹) (-(((x : ℂ)) ^ 2)⁻¹) x :=
    (hasDerivAt_inv hx0).comp_ofReal
  have h3 : HasDerivAt (fun y : ℝ => ((y : ℂ))⁻¹ * besselKernel ν y)
      ((-(((x : ℂ)) ^ 2)⁻¹) * besselKernel ν x + ((x : ℂ))⁻¹ * (-besselKernel (ν + 1) x + ν / (x : ℂ) * besselKernel ν x)) x :=
    hinv.mul hB
  have h4 := (hA.neg).add (h3.const_mul ν)
  have hg' : HasDerivAt g
      (-(-besselKernel (ν + 1 + 1) x + (ν + 1) / (x : ℂ) * besselKernel (ν + 1) x) +
        ν * ((-(((x : ℂ)) ^ 2)⁻¹) * besselKernel ν x +
          ((x : ℂ))⁻¹ * (-besselKernel (ν + 1) x + ν / (x : ℂ) * besselKernel ν x))) x := by
    refine h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    simp only [hg, Pi.add_apply, Pi.neg_apply]
    ring

  have h2' := LanglandsTunnell.ArchBessel.mul_besselKernel_eq_mul_sub (ν + 1) x hx
  rw [show ν + 1 - 1 = ν by ring] at h2'
  have hk2 : besselKernel (ν + 1 + 1) x = besselKernel ν x + 2 * ((ν + 1) / (x : ℂ) * besselKernel (ν + 1) x) := by
    have h5 : (ν + 1) / (x : ℂ) * besselKernel (ν + 1) x = (besselKernel (ν + 1 + 1) x - besselKernel ν x) / 2 := by
      rw [div_mul_eq_mul_div, div_eq_iff hx0, h2']; ring
    rw [h5]; ring
  refine (hg'.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [hdx, hk2]
  field_simp
  ring
