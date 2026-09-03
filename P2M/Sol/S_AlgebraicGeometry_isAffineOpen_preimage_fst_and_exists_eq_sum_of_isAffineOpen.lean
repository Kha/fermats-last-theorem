import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_AlgebraicGeometry_exists_algEquiv_sections_pullback_fst_preimage_tensor_of_isAffineOpen
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_isAffineOpen_preimage_fst_and_exists_eq_sum_of_isAffineOpen

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
p2m_open "TensorProduct P2MW.S_AlgebraicGeometry_isAffineOpen_preimage_fst_and_exists_eq_sum_of_isAffineOpen.TensorProduct"

namespace TensorProduct p2m_export "TensorProduct" "exists_finset map" end TensorProduct
p2m_open_scoped "TensorProduct" in

theorem TensorProduct.exists_fin_eq_sum_tmul {R : Type*} [CommSemiring R] {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (x : M ⊗[R] N) :
    ∃ (m : ℕ) (a : Fin m → M) (b : Fin m → N), x = ∑ i, a i ⊗ₜ[R] b i := by
  classical
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset x
  refine ⟨S.card, fun j => (S.equivFin.symm j).1.1, fun j => (S.equivFin.symm j).1.2, ?_⟩
  rw [hS, ← Finset.sum_coe_sort]
  exact Fintype.sum_equiv S.equivFin (fun s => s.1.1 ⊗ₜ[R] s.1.2) _ (fun s => by simp)

theorem solution
    {𝒪 C : Type} [CommRing 𝒪] [CommRing C] (φ : 𝒪 →+* C)
    {𝒳 : Scheme.{0}} (f : 𝒳 ⟶ Spec (CommRingCat.of 𝒪))
    (sC : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of 𝒪)) (hsC : sC = Spec.map (CommRingCat.ofHom φ))
    (V : 𝒳.Opens) (hV : IsAffineOpen V) :
    IsAffineOpen ((Limits.pullback.fst f sC) ⁻¹ᵁ V) ∧
    ∀ t : (Limits.pullback f sC).presheaf.obj (Opposite.op ((Limits.pullback.fst f sC) ⁻¹ᵁ V)),
      ∃ (m : ℕ) (a : Fin m → 𝒳.presheaf.obj (Opposite.op V)) (c : Fin m → C),
        t = ∑ i, ((Limits.pullback f sC).presheaf.map (homOfLE (le_top : (Limits.pullback.fst f sC) ⁻¹ᵁ V ≤ ⊤)).op).hom
              ((Limits.pullback.snd f sC).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (c i))) *
            ((Limits.pullback.fst f sC).app V).hom (a i) := by
  subst hsC
  letI : Algebra 𝒪 C := φ.toAlgebra
  letI instK : ∀ U : 𝒳.Opens, Algebra 𝒪 (𝒳.presheaf.obj (Opposite.op U)) := fun U =>
    Scheme.TwoAffineOpenCover.algebraOfHom f U
  letI instKP : ∀ W : (Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))).Opens,
      Algebra 𝒪 ((Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))).presheaf.obj (Opposite.op W)) :=
    fun W => Scheme.TwoAffineOpenCover.algebraOfHom
      (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) ≫ f) W
  obtain ⟨ε, hW, hε1, hε2, -⟩ :=
    AlgebraicGeometry.exists_algEquiv_sections_pullback_fst_preimage_tensor_of_isAffineOpen 𝒪 f C
  refine ⟨hW V hV, fun t => ?_⟩
  obtain ⟨m, a, c, h⟩ := TensorProduct.exists_fin_eq_sum_tmul (ε V hV t)
  refine ⟨m, a, c, (ε V hV).injective ?_⟩
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]
  have h1 : ε V hV (((Limits.pullback.fst f (Spec.map (CommRingCat.ofHom φ))).app V).hom (a i)) = a i ⊗ₜ[𝒪] (1 : C) :=
    hε1 V hV (a i)
  have h2 : ε V hV (((Limits.pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf.map
      (homOfLE (le_top : (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ V ≤ ⊤)).op).hom
      ((Limits.pullback.snd f (Spec.map (CommRingCat.ofHom φ))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (c i)))) = (1 : 𝒳.presheaf.obj (Opposite.op V)) ⊗ₜ[𝒪] c i :=
    hε2 V hV (c i)
  rw [h1, h2, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
