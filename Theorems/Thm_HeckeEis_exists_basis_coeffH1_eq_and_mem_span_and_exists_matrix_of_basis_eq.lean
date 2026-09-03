import Definitions.Def_Gamma0CoeffCohomologyEigen
import P2M.Util
import P2M.Sol.S_HeckeEis_exists_basis_coeffH1_eq_and_mem_span_and_exists_matrix_of_basis_eq

set_option autoImplicit false

open CongruenceSubgroup

theorem HeckeEis.exists_basis_coeffH1_eq_and_mem_span_and_exists_matrix_of_basis_eq
    {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type} [Field K] [Algebra R K] (hRK : Function.Injective (algebraMap R K))
    (N : ℕ) [Group.FG (Gamma0 N)]
    {Λ : Type} [AddCommGroup Λ] [Module R Λ] {V : Type} [AddCommGroup V] [Module K V]
    (ρR : Representation R (Gamma0 N) Λ) (ρ : Representation K (Gamma0 N) V)
    (ι : Λ →+ V) (hιs : ∀ (r : R) (x : Λ), ι (r • x) = algebraMap R K r • ι x)
    (hιρ : ∀ (γ : Gamma0 N) (x : Λ), ι (ρR γ x) = ρ γ (ι x))
    {d : ℕ} (bΛ : Module.Basis (Fin d) R Λ) (bV : Module.Basis (Fin d) K V)
    (hb : ∀ j : Fin d, bV j = ι (bΛ j))
    (Φ : HeckeEis.coeffH1 ρR →+ HeckeEis.coeffH1 ρ)
    (hΦ : ∀ z : ↥(HeckeEis.coeffCocycles ρR), ∃ w : ↥(HeckeEis.coeffCocycles ρ),
      (∀ γ : Gamma0 N, (w : Gamma0 N → V) γ = ι ((z : Gamma0 N → Λ) γ)) ∧
        Φ (HeckeEis.coeffH1Mk ρR z) = HeckeEis.coeffH1Mk ρ w)
    {I : Type} (TR : I → (HeckeEis.coeffH1 ρR →+ HeckeEis.coeffH1 ρR))
    (T : I → (HeckeEis.coeffH1 ρ →+ HeckeEis.coeffH1 ρ))
    (hT : ∀ (l : I) (x : HeckeEis.coeffH1 ρR), Φ (TR l x) = T l (Φ x)) :
    ∃ (t : ℕ) (b : Fin t → HeckeEis.coeffH1 ρR) (c : Module.Basis (Fin t) K (HeckeEis.coeffH1 ρ)),
      (∀ i : Fin t, c i = Φ (b i)) ∧
        (∀ x : HeckeEis.coeffH1 ρR, ∃ r : Fin t → R, Φ x = ∑ i : Fin t, algebraMap R K (r i) • c i) ∧
          ∀ l : I, ∃ A : Matrix (Fin t) (Fin t) R,
            ∀ j : Fin t, T l (c j) = ∑ i : Fin t, algebraMap R K (A i j) • c i := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_exists_basis_coeffH1_eq_and_mem_span_and_exists_matrix_of_basis_eq.solution
