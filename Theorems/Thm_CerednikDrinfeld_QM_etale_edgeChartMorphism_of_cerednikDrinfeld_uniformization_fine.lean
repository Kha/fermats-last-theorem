import Definitions.Def_CerednikDrinfeld_AlgFunctorConst
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_etale_edgeChartMorphism_of_cerednikDrinfeld_uniformization_fine
attribute [-instance] CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.QM.etale_edgeChartMorphism_of_cerednikDrinfeld_uniformization_fine
    {r : ℕ} [Fact r.Prime]

    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]

    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})

    (G : Type)
    (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪)) [LocallyOfFiniteType fM]
    (Θf : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B → (Scheme.nilpPoints fM).obj B)
    (hnat :
      ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B),
          Θf B' hB' ((AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map φ x) = (Scheme.nilpPoints fM).map φ (Θf B hB x))
    (het :
      ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B₀ : Type) [CommRing B₀] [Algebra 𝒪 B₀] (p : B →ₐ[𝒪] B₀)
          (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB₀ : IsNilpotent (algebraMap 𝒪 B₀ π)),
          Function.Surjective p → (∀ s t : B, p s = 0 → p t = 0 → s * t = 0) →
          ∀ (x₀ : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B₀) (y : (Scheme.nilpPoints fM).obj B), (Scheme.nilpPoints fM).map p y = Θf B₀ hB₀ x₀ →
            ∃! x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B, (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map p x = x₀ ∧ Θf B hB x = y)

    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])

    (C : Type) [CommRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π)) (ψ : Onr →ₐ[𝒪] C)
    (N : Scheme.{0}) (p₁ : N ⟶ M) (p₂ : N ⟶ Spec (CommRingCat.of C)) (hN : IsPullback p₁ p₂ fM (Scheme.specOver C))

    [Algebra 𝒪 (chartERing C (algebraMap 𝒪 C π) r)] [IsScalarTower 𝒪 C (chartERing C (algebraMap 𝒪 C π) r)]
    (hR : IsNilpotent (algebraMap 𝒪 (chartERing C (algebraMap 𝒪 C π) r) π))

    (d : DeligneDatum (K := K₀) π (chartERing C (algebraMap 𝒪 C π) r))
    (hd₀ : d.line (stdFullLattice K₀) =
      Submodule.span (chartERing C (algebraMap 𝒪 C π) r)
        {(chartERing.ξ C (algebraMap 𝒪 C π) r) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : chartERing C (algebraMap 𝒪 C π) r) ⊗ₜ[𝒪] stdBasisVec K₀ 1})
    (hd₁ : d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
      (Submodule.span (chartERing C (algebraMap 𝒪 C π) r)
        {(1 : chartERing C (algebraMap 𝒪 C π) r) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (chartERing.η C (algebraMap 𝒪 C π) r) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
        (actBaseChange (chartERing C (algebraMap 𝒪 C π) r) g₁ (stdFullLattice K₀)).toLinearMap)
    (hdE : d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀))

    (g : G) (h : Matrix.GeneralLinearGroup (Fin 2) K₀)
    (θ : Spec (CommRingCat.of (chartERing C (algebraMap 𝒪 C π) r)) ⟶ N)
    (hθ₁ : θ ≫ p₁ = (Θf (chartERing C (algebraMap 𝒪 C π) r) hR
      (((IsScalarTower.toAlgHom 𝒪 C (chartERing C (algebraMap 𝒪 C π) r)).comp ψ,
        (Omega.action K₀ π).act (chartERing C (algebraMap 𝒪 C π) r) h d), g)).1)
    (hθ₂ : θ ≫ p₂ = Spec.map (CommRingCat.ofHom (algebraMap C (chartERing C (algebraMap 𝒪 C π) r)))) :
    Etale θ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_etale_edgeChartMorphism_of_cerednikDrinfeld_uniformization_fine.solution
