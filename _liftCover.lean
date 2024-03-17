import Mathlib.Topology.ContinuousFunction.Basic

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

variable {ι : Type*} [Finite ι] (S : ι → Set α) (φ : ∀ i : ι, C(S i, β))
(hφ : ∀ (i j) (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), φ i ⟨x, hxi⟩ = φ j ⟨x, hxj⟩)
(hS_cover : ∀ x : α, ∃ i, x ∈ S i)
(hS_closed : ∀ i, IsClosed (S i))

noncomputable def liftCover_closed : C(α, β) :=
  have H : ⋃ i, S i = Set.univ := Set.iUnion_eq_univ_iff.2 hS_cover
  let Φ := Set.liftCover S (fun i ↦ φ i) hφ H
  ContinuousMap.mk Φ <| continuous_iff_isClosed.mpr fun Y hY ↦ by
    have : ∀ i, φ i ⁻¹' Y = S i ∩ Φ ⁻¹' Y := fun i ↦ by
      ext x
      simp
      constructor
      . intro ⟨hxi, hφx⟩
        have : Φ x = φ i ⟨x, hxi⟩ := Set.liftCover_of_mem hxi
        rw [← this] at hφx
        trivial
      . intro ⟨hxi, hφx⟩
        use hxi
        have : Φ x = φ i ⟨x, hxi⟩ := Set.liftCover_of_mem hxi
        rwa [← this]
    have : Φ ⁻¹' Y = ⋃ i, Subtype.val '' (φ i ⁻¹' Y) := by
      conv => rhs; ext x; arg 1; ext i; rw [this]
      conv => rhs; ext x; rw [← Set.iUnion_inter, H]; simp
    rw [this]
    exact isClosed_iUnion_of_finite fun i ↦
      IsClosed.trans (IsClosed.preimage (φ i).continuous hY) (hS_closed i)
