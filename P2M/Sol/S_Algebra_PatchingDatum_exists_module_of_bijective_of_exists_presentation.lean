import Theorems.Thm_Algebra_PatchingDatum_nonempty_of_exists_presentation_of_free
import P2M.Util
namespace P2MW.S_Algebra_PatchingDatum_exists_module_of_bijective_of_exists_presentation

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (ℓ : ℕ) {R : Type} [CommRing R] [Algebra 𝒪 R]
    {T : Type} [CommRing T] [Nontrivial T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
    (φ : R →ₐ[𝒪] T) (hφ : Function.Bijective φ)
    (hCI : ∃ (n : ℕ) (f : Fin n → MvPowerSeries (Fin n) 𝒪),
      Nonempty ((MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range f)) ≃ₐ[𝒪] T)) :
    ∃ (M : Type) (_ : AddCommGroup M) (_ : Module R M) (_ : Module T M) (_ : Nontrivial M),
      (∀ (x : R) (m : M), φ x • m = x • m) ∧
      ∃ r : ℕ, Nonempty (Algebra.PatchingDatum 𝒪 ℓ r R M) := by
  obtain ⟨n, f, ⟨e⟩⟩ := hCI

  let ψ : R ≃ₐ[𝒪] T := AlgEquiv.ofBijective φ hφ
  haveI : Module.Finite 𝒪 R := Module.Finite.equiv ψ.symm.toLinearEquiv
  haveI : Module.Free 𝒪 R := Module.Free.of_equiv ψ.symm.toLinearEquiv

  have hCI' : ∃ g : Fin n → MvPowerSeries (Fin n) 𝒪,
      Nonempty ((MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range g)) ≃ₐ[𝒪] R) :=
    ⟨f, ⟨e.trans ψ.symm⟩⟩

  letI instRT : Module R T := Module.compHom T (φ : R →+* T)
  let η : R ≃ₗ[R] T :=
    { ψ.toEquiv with
      map_add' := fun x y => map_add φ x y
      map_smul' := fun x y => map_mul φ x y }
  haveI : Module.Free R T := Module.Free.of_equiv η
  haveI : Module.Finite R T := Module.Finite.equiv η
  obtain ⟨P⟩ := Algebra.PatchingDatum.nonempty_of_exists_presentation_of_free ℓ hCI' T
  exact ⟨T, inferInstance, instRT, inferInstance, inferInstance, fun _ _ => rfl, n, ⟨P⟩⟩

