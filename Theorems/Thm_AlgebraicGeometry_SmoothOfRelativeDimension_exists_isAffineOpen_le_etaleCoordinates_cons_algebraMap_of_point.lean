import Mathlib
import Definitions.Def_AlgebraicGeometry_KaehlerModule
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SmoothOfRelativeDimension_exists_isAffineOpen_le_etaleCoordinates_cons_algebraMap_of_point
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Opposite

theorem AlgebraicGeometry.SmoothOfRelativeDimension.exists_isAffineOpen_le_etaleCoordinates_cons_algebraMap_of_point
    (Sc : Type) [CommRing Sc] [IsDomain Sc] [Algebra ℂ Sc] [Algebra.FiniteType ℂ Sc]
    (hSc : Algebra.Smooth ℂ Sc) (hΩ : Module.rank Sc (KaehlerDifferential ℂ Sc) = 1) (t : Sc)
    {G : Scheme.{0}} (f : G ⟶ Spec (CommRingCat.of Sc)) {g : ℕ} (hsm : SmoothOfRelativeDimension g f)
    (σ₁ : Sc →ₐ[ℂ] ℂ)
    (hdt₁ : (RingHom.ker σ₁.toRingHom) • (⊤ : Submodule Sc (KaehlerDifferential ℂ Sc)) ⊔
        Submodule.span Sc {KaehlerDifferential.D ℂ Sc t} = ⊤)
    (P₀ : Spec (CommRingCat.of ℂ) ⟶ G) (hP₀ : P₀ ≫ f = Spec.map (CommRingCat.ofHom σ₁.toRingHom))
    (O : G.Opens) (hO : ⊤ ≤ P₀ ⁻¹ᵁ O) :
    ∃ (U : G.Opens) (hU : IsAffineOpen U) (hUO : U ≤ O) (hP₀U : ⊤ ≤ P₀ ⁻¹ᵁ U),
      letI : Algebra Sc Γ(G, U) := f.sectionsAlgebra U
      letI : Algebra ℂ Γ(G, U) := (f ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ Sc))).sectionsAlgebra U
      IsScalarTower ℂ Sc Γ(G, U) ∧
      IsDomain Γ(G, U) ∧ Algebra.FiniteType ℂ Γ(G, U) ∧ Algebra.Smooth ℂ Γ(G, U) ∧
      Module.rank Γ(G, U) (KaehlerDifferential ℂ Γ(G, U)) = ((g + 1 : ℕ) : Cardinal) ∧
      ∃ (χ₀ : Γ(G, U) →ₐ[ℂ] ℂ) (s : Fin g → Γ(G, U)),
        (∀ b : Γ(G, U), χ₀ b = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((P₀.appLE U ⊤ hP₀U) b)) ∧
        (∀ a : Sc, χ₀ (algebraMap Sc Γ(G, U) a) = σ₁ a) ∧
        (RingHom.ker χ₀.toRingHom) • (⊤ : Submodule Γ(G, U) (KaehlerDifferential ℂ Γ(G, U))) ⊔
          Submodule.span Γ(G, U) (Set.range fun i : Fin (g + 1) =>
            KaehlerDifferential.D ℂ Γ(G, U) ((Fin.cons (algebraMap Sc Γ(G, U) t) s : Fin (g + 1) → Γ(G, U)) i)) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SmoothOfRelativeDimension_exists_isAffineOpen_le_etaleCoordinates_cons_algebraMap_of_point.solution
