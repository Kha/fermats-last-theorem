import Definitions.Def_AlgebraicGeometry_ThetaReframe
import Definitions.Def_AlgebraicGeometry_ProjSpace
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_IsReframe_isUnit

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {g N n : ℕ} {S : Type} [CommRing S] {X X' : FramedPolarisedAbelianScheme g N n S}
    {U : Matrix (Fin (N + 1)) (Fin (N + 1)) S} (h : X.IsReframe U X') : IsUnit U := by
  classical
  obtain ⟨P', h₁, h₂, -, hσ⟩ := h

  set ρ : S → ↑(X.A.presheaf.obj (Opposite.op ⊤)) :=
    fun s => (X.f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom s) with hρ
  have hρmul : ∀ s t : S, ρ (s * t) = ρ s * ρ t := fun s t => by simp only [hρ, map_mul]
  have hρsum : ∀ (v : Fin (N + 1) → S), ρ (∑ i, v i) = ∑ i, ρ (v i) := fun v => by simp only [hρ, map_sum]

  have hB := X.frame_basis
  have hB' : Function.Bijective fun c : Fin (N + 1) → S => ∑ i, ρ (c i) • P'.σ i := h₂
  have hBσ : Function.Bijective fun c : Fin (N + 1) → S => ∑ i, ρ (c i) • X.frame.σ i := hB

  have hcomp : (fun c : Fin (N + 1) → S => ∑ i, ρ (c i) • P'.σ i) =
      (fun c : Fin (N + 1) → S => ∑ i, ρ (c i) • X.frame.σ i) ∘ (fun v => Matrix.vecMul v U) := by
    funext c
    simp only [Function.comp_apply]
    have hσ' : ∀ i, P'.σ i = ∑ j, ρ (U i j) • X.frame.σ j := hσ
    simp_rw [hσ', Finset.smul_sum, smul_smul, ← hρmul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_smul, ← hρsum]
    rfl
  have hv : Function.Surjective (fun v : Fin (N + 1) → S => Matrix.vecMul v U) := by
    intro w
    obtain ⟨c, hc⟩ := hB'.2 ((fun c : Fin (N + 1) → S => ∑ i, ρ (c i) • X.frame.σ i) w)
    rw [hcomp] at hc
    exact ⟨c, hBσ.1 hc⟩
  exact Matrix.vecMul_surjective_iff_isUnit.1 hv
