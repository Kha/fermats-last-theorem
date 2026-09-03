import Definitions.Def_LanglandsTunnell_ArtinFrobenius
import P2M.Util
import P2M.Sol.S_LT_Artin_eq_artinFrob_of_isArithFrobAt

set_option autoImplicit false

theorem LT.Artin.eq_artinFrob_of_isArithFrobAt
    (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    [IsMulCommutative (M ≃ₐ[K] M)] {σ : M ≃ₐ[K] M} {Q : Ideal (NumberField.RingOfIntegers M)}
    [Q.IsPrime] (H : IsArithFrobAt (NumberField.RingOfIntegers K) σ Q)
    (hQ : Q.under (NumberField.RingOfIntegers K) = v.asIdeal)
    (hI : Q.inertia (M ≃ₐ[K] M) = ⊥) :
    σ = LanglandsTunnell.P2.Artin.artinFrob K M v := by p2m_exact_reverting @_root_.P2MW.S_LT_Artin_eq_artinFrob_of_isArithFrobAt.solution
