import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_isFlatAt_of_forall_point_of_finite_index
attribute [-instance] instIsScalarTowerTensorProduct_definitions
attribute [-simp] closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff

open scoped TensorProduct

theorem GaloisRepAdic.isFlatAt_of_forall_point_of_finite_index
    {P : Type} [CommRing P] [IsLocalRing P] {n : ℕ} {A : Fin n → Type}
    [∀ i, CommRing (A i)] [∀ i, IsLocalRing (A i)]
    (χ : ∀ i, P →+* A i) (hχ : ∀ i, IsLocalHom (χ i))
    (hinj : ∀ x, (∀ i, χ i x = 0) → x = 0)
    {p c : ℕ} (hpP : (p : P) ∈ IsLocalRing.maximalIdeal P)
    (hidx : ∀ a : ∀ i, A i, ∃ x : P, ∀ i, χ i x = (p : A i) ^ c * a i)
    (hAfin : ∀ i, Finite (A i ⧸ Ideal.span {(p : A i)}))
    (ρ : GaloisRepAdic P) (hflat : ∀ i, (ρ.baseChangeAlong (χ i) (hχ i)).IsFlatAt p) :
    ρ.IsFlatAt p := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_isFlatAt_of_forall_point_of_finite_index.solution
