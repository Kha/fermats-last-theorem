import Mathlib
import Definitions.Def_Deformations_ClosedSubalgebra
import Definitions.Def_Deformations_ConjQuotSubfunctor
import P2M.Util
import P2M.Sol.S_Deformation_exists_cond_lift_traceAlgebra

open CategoryTheory IsLocalRing

universe u v
theorem Deformation.exists_cond_lift_traceAlgebra {n : Type} [Fintype n] [DecidableEq n] {G : Type u} [Group G]
    [TopologicalSpace G] {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞] [Finite (IsLocalRing.ResidueField 𝓞)]
    {F : CategoryTheory.Subfunctor (Deformation.repnFunctor n G 𝓞)} (hconj : Deformation.ConjStable n F)
    (hrefl : Deformation.ReflectedByInjective n F) {A : Deformation.ProartinianCat 𝓞} {ρ' : G →ₜ* GL n A}
    (hρ' : ρ' ∈ F.obj A) (hdesc : Deformation.TraceAlgebra.Descends ρ') :
    ∃ σ : G →ₜ* GL n (Deformation.TraceAlgebra.obj ρ'),
      σ ∈ F.obj (Deformation.TraceAlgebra.obj ρ') ∧
      Deformation.traceSubalgebra 𝓞 σ = ⊤ ∧
      (Quotient.mk'' (Deformation.mapRepn n G 𝓞 (Deformation.TraceAlgebra.ι ρ') σ) :
        (Deformation.repnQuotFunctor n G 𝓞).obj A) = Quotient.mk'' ρ' := by p2m_exact_reverting @_root_.P2MW.S_Deformation_exists_cond_lift_traceAlgebra.solution
