import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_nsmul_pow_eq_one_of_isInfinitesimal

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.nsmul_pow_eq_one_of_isInfinitesimal
    {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)} (L : RelativeGroupLaw B f)
    {g : ℕ} (F : MvFormalGroup g B) (θ : RelativeGroupLaw.FormalCoordinates f g) (hθ : L.IsFormalCoordinates F θ)
    {B' : Type} [CommRing B'] [Algebra B B'] (N : ℕ) (hN : (N : B') = 0)
    (J : Ideal B') (μ : ℕ) (hJ : J ^ (μ + 1) = ⊥)
    (P : SchemeHomOver (Scheme.specOver (𝒪 := B) B') f) (hP : L.IsInfinitesimal J P) :
    L.nsmul (Scheme.specOver (𝒪 := B) B') (N ^ μ) P = L.one (Scheme.specOver (𝒪 := B) B') := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_nsmul_pow_eq_one_of_isInfinitesimal.solution
