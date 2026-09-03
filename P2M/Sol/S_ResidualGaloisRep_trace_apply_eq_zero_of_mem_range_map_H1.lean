import Mathlib
import Definitions.Def_GaloisRep_AdZero
import P2M.Util
namespace P2MW.S_ResidualGaloisRep_trace_apply_eq_zero_of_mem_range_map_H1

set_option autoImplicit false

open CategoryTheory groupCohomology

theorem solution
    {k : Type} [Field k] (ρbar : ResidualGaloisRep k)
    {G : Type} [Group G] (f : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (φ : Rep.res f ρbar.adZero ⟶ Rep.res f (Rep.of ρbar.adRep))
    (hφ : ∀ x : LinearMap.ker (LinearMap.trace k ρbar.V), φ.hom x = (x : Module.End k ρbar.V))
    (c : cocycles₁ (Rep.res f (Rep.of ρbar.adRep)))
    (hc : (H1π (Rep.res f (Rep.of ρbar.adRep))).hom c ∈
      LinearMap.range (groupCohomology.map (A := Rep.res f ρbar.adZero) (MonoidHom.id G) φ 1).hom)
    (σ : G) :
    LinearMap.trace k ρbar.V ((c : G → Module.End k ρbar.V) σ) = 0 := by
  obtain ⟨x, hx⟩ := hc
  obtain ⟨c0, rfl⟩ : ∃ c0 : cocycles₁ (Rep.res f ρbar.adZero), (H1π _).hom c0 = x :=
    H1_induction_on x fun c0 => ⟨c0, rfl⟩
  have hval : ∀ τ, (mapCocycles₁ (MonoidHom.id G) φ c0) τ =
      ((c0 τ : LinearMap.ker (LinearMap.trace k ρbar.V)) : Module.End k ρbar.V) :=
    fun τ => hφ (c0 τ)
  erw [H1π_comp_map_apply] at hx
  rw [H1π_eq_iff] at hx
  obtain ⟨m, hm⟩ := hx
  have hmσ := congrFun hm σ
  rw [d₀₁_hom_apply] at hmσ

  simp only [Pi.sub_apply, hval] at hmσ
  have hcσ : (c : G → Module.End k ρbar.V) σ =
      ((c0 σ : LinearMap.ker (LinearMap.trace k ρbar.V)) : Module.End k ρbar.V) -
        ((Rep.res f (Rep.of ρbar.adRep)).ρ σ m - m) := by
    rw [hmσ]; abel
  have htr0 : LinearMap.trace k ρbar.V
      ((c0 σ : LinearMap.ker (LinearMap.trace k ρbar.V)) : Module.End k ρbar.V) = 0 :=
    (c0 σ).2
  have htrm : LinearMap.trace k ρbar.V ((Rep.res f (Rep.of ρbar.adRep)).ρ σ m) =
      LinearMap.trace k ρbar.V m :=
    ρbar.trace_adRep_apply (f σ) m
  rw [hcσ, map_sub, map_sub, htr0, htrm, sub_self, sub_zero]
