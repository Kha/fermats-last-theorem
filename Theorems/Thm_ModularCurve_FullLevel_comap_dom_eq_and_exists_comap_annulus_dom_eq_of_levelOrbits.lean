import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_comap_dom_eq_and_exists_comap_annulus_dom_eq_of_levelOrbits

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.comap_dom_eq_and_exists_comap_annulus_dom_eq_of_levelOrbits
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (FSS : Type) [Field FSS] [Algebra (ResidueField A) FSS]
    (R : RegularProlongation A ↥(fieldBar q M') FSS)
    (hint : ∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      R.integers.comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom = R.integers)
    (N : Finset (Place (ResidueField A) FSS)) (hN : N.card = q + 1)
    (Dx : Place (ResidueField A) FSS → Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M')))

    (heqv : ∀ τ ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
        ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
      ∀ (hτ : ∀ f : ↥(fieldBar q M'), τ f ∈ R.integers ↔ f ∈ R.integers) (Q : Place (ResidueField ↥A) FSS),
        (R.resAut τ hτ • Q ∈ N ↔ Q ∈ N) ∧
        (Q ∉ N → AlgebraicCurve.RegularProlongation.smulDisc τ (Dx Q) = Dx (R.resAut τ hτ • Q)))

    (htrans : ∀ x x' : Place (ResidueField ↥A) FSS, x ∈ N → x' ∈ N →
      ∃ (ζ : Idx q) (γ : SL(2, ℤ)) (_ : γ ∈ Gamma0 M')
        (hτ : ∀ f : ↥(fieldBar q M'), levelAutBar q M' ζ γ f ∈ R.integers ↔ f ∈ R.integers),
        R.resAut (levelAutBar q M' ζ γ) hτ • x = x')

    (An : Place (ResidueField ↥A) FSS → Annulus A ↥(fieldBar q M'))
    (hAn : ∀ τ ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
        ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
      ∀ (hτ : ∀ f : ↥(fieldBar q M'), τ f ∈ R.integers ↔ f ∈ R.integers), ∀ x ∈ N,
        AlgebraicCurve.RegularProlongation.smulDisc τ (An x).dom = (An (R.resAut τ hτ • x)).dom)

    (C : ComponentChart A ↥(fieldBar q M') FSS)
    (hCR : C.integers = R.integers)
    (hdom : ∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P ∈ C.dom ↔ ∃ Q, Q ∉ N ∧ P ∈ Dx Q) :

    (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → (C.comap (levelAutBar q M' ζ γ)).integers = C.integers) ∧

    (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → (C.comap (levelAutBar q M' ζ γ)).dom = C.dom) ∧

    (∀ x : ↥N, ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ ∃ x' : ↥N, x' ≠ x ∧
      ((An (x : Place (ResidueField A) FSS)).comap (levelAutBar q M' ζ γ)).dom = (An (x' : Place (ResidueField A) FSS)).dom) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_comap_dom_eq_and_exists_comap_annulus_dom_eq_of_levelOrbits.solution
