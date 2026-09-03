import Definitions.Def_ModularCurve_JZeroNeronIdentityComponent
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import P2M.Util
import P2M.Sol.S_ModularCurve_JZeroNeronIdentityComponent_small_fppfCohomology_one_kernel_zsmul

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme NeronModelInfra GoodReductionJacobian ModularCurve

theorem ModularCurve.JZeroNeronIdentityComponent.small_fppfCohomology_one_kernel_zsmul
    (p : ℕ) [Fact p.Prime] (N : JZeroNeronIdentityComponent p)
    (𝒢 : Sheaf (smallFppfTopology specInt) Ab.{1})
    (e : ∀ U : specInt.Fppf, 𝒢.1.obj (op U) ≃ SchemeHomOver U.hom N.g)
    (he : ∀ {U V : specInt.Fppf} (k : U ⟶ V) (s : 𝒢.1.obj (op V)),
        e U (𝒢.1.map k.op s) = schemeHomOverComp k.left (MorphismProperty.Over.w k) (e V s))
    (n : ℤ) :
    Small.{0} (fppfCohomology specInt (kernel (n • 𝟙 𝒢)) 1) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZeroNeronIdentityComponent_small_fppfCohomology_one_kernel_zsmul.solution
