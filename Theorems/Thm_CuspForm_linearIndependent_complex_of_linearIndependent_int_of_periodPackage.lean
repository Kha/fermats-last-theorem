import Definitions.Def_CuspForm_HeckeAlgebra
import P2M.Util
import P2M.Sol.S_CuspForm_linearIndependent_complex_of_linearIndependent_int_of_periodPackage
set_option autoImplicit false

theorem CuspForm.linearIndependent_complex_of_linearIndependent_int_of_periodPackage (N : ℕ) [NeZero N] (k : ℤ)
    {V : Type} [AddCommGroup V] [Module ℂ V] {X : Type}
    (ev : V →ₗ[ℂ] (X → ℂ)) (hev : Function.Injective ev)
    (P : CuspForm (CongruenceSubgroup.Gamma0 N) k →ₗ[ℂ] V) (hP : Function.Injective P)
    (σ : V →ₗ[ℂ] V) (L : AddSubgroup V)
    (hLrat : ∀ v ∈ L, ∀ x : X, ∃ q : ℚ, ev v x = (q : ℂ))
    (hLspan : ∀ f : CuspForm (CongruenceSubgroup.Gamma0 N) k, P f ∈ Submodule.span ℂ (L : Set V))
    (hLcover : ∀ v ∈ L, ∃ f g : CuspForm (CongruenceSubgroup.Gamma0 N) k, v = P f + σ (P g))
    (htwin : ∀ t ∈ CuspForm.heckeGenerators N k (∅ : Set ℕ), ∃ A : V →ₗ[ℂ] V,
      (∀ f : CuspForm (CongruenceSubgroup.Gamma0 N) k, P (t f) = A (P f)) ∧
      (∀ v : V, A (σ v) = σ (A v)) ∧ (∀ v ∈ L, A v ∈ L))
    {ι : Type} (T : ι → CuspForm.heckeAlgebra N k (∅ : Set ℕ)) (hT : LinearIndependent ℤ T) :
    LinearIndependent ℂ
      (fun i => ((T i : CuspForm.heckeAlgebra N k (∅ : Set ℕ)) :
        Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k))) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_linearIndependent_complex_of_linearIndependent_int_of_periodPackage.solution
