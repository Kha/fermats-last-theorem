import Definitions.Def_Representation_AbsolutelyIrreducible
import P2M.Util
namespace P2MW.S_Representation_injective_liftBaseChange_of_isAbsolutelyIrreducible

set_option autoImplicit false

open scoped TensorProduct

theorem solution
    {F k G V W : Type} [Field F] [Field k] [Algebra F k] [Group G]
    [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module k W] [Module F W] [IsScalarTower F k W]
    (ρ : Representation F G V) [Representation.IsAbsolutelyIrreducible.{0} ρ]
    (τ : Representation k G W)
    (ι : V →ₗ[F] W) (hι : Function.Injective ι)
    (hιG : ∀ (g : G) (v : V), ι (ρ g v) = τ g (ι v)) :
    Function.Injective (ι.liftBaseChange k) := by
  have hcomm : ∀ (g : G) (x : k ⊗[F] V),
      ι.liftBaseChange k ((ρ g).baseChange k x) = τ g (ι.liftBaseChange k x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c v => simp [hιG]
    | add x y hx hy => simp [hx, hy]
  obtain ⟨f, hf⟩ : ∃ f : Representation.IntertwiningMap (Representation.baseChange k ρ) τ,
      (⇑f : k ⊗[F] V → W) = ⇑(ι.liftBaseChange k) :=
    ⟨(ι.liftBaseChange k).intertwiningMap_of_isIntertwiningMap (Representation.baseChange k ρ) τ
        (fun g x => hcomm g x), rfl⟩
  haveI : Representation.IsIrreducible (Representation.baseChange k ρ) :=
    Representation.IsAbsolutelyIrreducible.absolutelyIrreducible k inferInstance inferInstance
  rw [← hf]
  rcases Representation.IsIrreducible.injective_or_eq_zero f with h | h
  · exact h
  · have hV : ∀ v : V, v = 0 := fun v => hι (by
      have h1 := congrFun hf ((1 : k) ⊗ₜ[F] v)
      rw [h] at h1
      simpa using h1.symm)
    haveI : Subsingleton V := ⟨fun a b => (hV a).trans (hV b).symm⟩
    exact Function.injective_of_subsingleton _

#print axioms solution
