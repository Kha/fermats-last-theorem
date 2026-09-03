import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Theorems.Thm_AlgebraicGeometry_Scheme_nilpPoints_forall_isNoetherianRing_eq_of_forall_eq_of_forall_isIdempotentElem
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_nilpPoints_forall_eq_of_forall_eq_of_isNoetherianRing_of_forall_isIdempotentElem

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry CerednikDrinfeld.FormalOmega

theorem solution
    {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) (F : AlgFunctor 𝒪)
    {N : Scheme.{0}} (fN : N ⟶ Spec (CommRingCat.of 𝒪))

    (hF : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → ∀ x : F.obj B,
      ∃ (S : Subalgebra 𝒪 B) (_ : IsNoetherianRing ↥S) (x₀ : F.obj ↥S), F.map S.val x₀ = x)

    (u₁ u₂ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → F.obj B → (Scheme.nilpPoints fN).obj B)
    (hu₁ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B']
      (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : F.obj B),
      u₁ B' hB' (F.map φ x) = (Scheme.nilpPoints fN).map φ (u₁ B hB x))
    (hu₂ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B']
      (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : F.obj B),
      u₂ B' hB' (F.map φ x) = (Scheme.nilpPoints fN).map φ (u₂ B hB x))

    (heq : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)),
      (∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) → ∀ x : F.obj B, u₁ B hB x = u₂ B hB x) :
    ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : F.obj B), u₁ B hB x = u₂ B hB x := by
  intro B _ _ hB x
  obtain ⟨S, hSN, x₀, rfl⟩ := hF B hB x
  haveI : IsNoetherianRing ↥S := hSN
  have hS : IsNilpotent (algebraMap 𝒪 ↥S π) := by
    obtain ⟨n, hn⟩ := hB
    refine ⟨n, Subtype.ext ?_⟩
    have h1 : (S.val (algebraMap 𝒪 ↥S π ^ n) : B) = algebraMap 𝒪 B π ^ n := by
      rw [map_pow, AlgHom.commutes]
    rw [Subalgebra.coe_val] at h1
    rw [h1, hn]
    rfl
  rw [hu₁ ↥S B hS hB S.val x₀, hu₂ ↥S B hS hB S.val x₀]
  congr 1
  exact AlgebraicGeometry.Scheme.nilpPoints.forall_isNoetherianRing_eq_of_forall_eq_of_forall_isIdempotentElem π F fN
    (fun B _ _ _ hB x => u₁ B hB x) (fun B _ _ _ hB x => u₂ B hB x)
    (fun B _ _ _ B' _ _ _ hB hB' φ x => hu₁ B B' hB hB' φ x)
    (fun B _ _ _ B' _ _ _ hB hB' φ x => hu₂ B B' hB hB' φ x)
    (fun B _ _ _ hB hc x => heq B hB hc x) ↥S hS x₀
