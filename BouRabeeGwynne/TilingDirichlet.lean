module

-- Copied from Leonardo Bonanno's (leobon12) formalization of this paper,
-- https://github.com/leobon12/lean-formalizations/tree/main/results/bou-rabee-gwynne
-- (file `BouRabeeGwynne/TilingDirichlet.lean` at commit cf73d6e); unchanged apart from this header.
public import BouRabeeGwynne.TilingNetwork

@[expose] public section

open scoped Classical

namespace BouRabeeGwynne
namespace OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

/-- A finite closed graph region already contains every neighbor of its interior
vertices, so their neighbor sets are finite. -/
theorem neighbors_finite_of_finite_closed {U : Set (Euc d)}
    [Fintype (T.closedVertices U)] {v : T.V} (hv : v ∈ T.interiorVertices U) :
    (T.neighbors v).Finite :=
  (Set.toFinite (T.closedVertices U)).subset (fun _ hw => T.neighbor_mem_closedVertices hv hw)

/-- The actual finite Dirichlet solution, extended to all tiling vertices by the
supplied data away from the closed graph region. -/
noncomputable def dirichletSolution (U : Set (Euc d)) [Fintype (T.closedVertices U)]
    (haccess : (T.finiteNetwork (T.closedVertices U)).BoundaryAccessible (T.finiteInterior U))
    (g : T.V → ℝ) (v : T.V) : ℝ :=
  if hv : v ∈ T.closedVertices U then
    (T.finiteNetwork (T.closedVertices U)).dirichletSolution (T.finiteInterior U)
      haccess (fun w => g w) ⟨v, hv⟩
  else g v

@[simp] theorem dirichletSolution_apply_closed (U : Set (Euc d))
    [Fintype (T.closedVertices U)]
    (haccess : (T.finiteNetwork (T.closedVertices U)).BoundaryAccessible (T.finiteInterior U))
    (g : T.V → ℝ) (v : T.closedVertices U) :
    T.dirichletSolution U haccess g v =
      (T.finiteNetwork (T.closedVertices U)).dirichletSolution (T.finiteInterior U)
        haccess (fun w => g w) v := by
  simp [dirichletSolution, v.property]

theorem dirichletSolution_apply_outside (U : Set (Euc d))
    [Fintype (T.closedVertices U)]
    (haccess : (T.finiteNetwork (T.closedVertices U)).BoundaryAccessible (T.finiteInterior U))
    (g : T.V → ℝ) {v : T.V} (hv : v ∉ T.closedVertices U) :
    T.dirichletSolution U haccess g v = g v := by
  simp [dirichletSolution, hv]

/-- The selected ambient function solves the paper's finite Dirichlet problem. -/
theorem dirichletSolution_spec (U : Set (Euc d)) [Fintype (T.closedVertices U)]
    (haccess : (T.finiteNetwork (T.closedVertices U)).BoundaryAccessible (T.finiteInterior U))
    (g : T.V → ℝ) : T.SolvesDirichlet U g (T.dirichletSolution U haccess g) := by
  apply (T.solvesDirichlet_iff_restrict
    (fun _ hv => T.neighbors_finite_of_finite_closed hv) g _).mpr
  simpa only [T.dirichletSolution_apply_closed] using
    (T.finiteNetwork (T.closedVertices U)).dirichletSolution_spec (T.finiteInterior U)
      haccess (fun w => g w)

theorem exists_dirichlet (U : Set (Euc d)) [Fintype (T.closedVertices U)]
    (haccess : (T.finiteNetwork (T.closedVertices U)).BoundaryAccessible (T.finiteInterior U))
    (g : T.V → ℝ) : ∃ f : T.V → ℝ, T.SolvesDirichlet U g f :=
  ⟨T.dirichletSolution U haccess g, T.dirichletSolution_spec U haccess g⟩

/-- Any other solution agrees with the selected solution on the entire closed
graph region. Values at unrelated tiling vertices remain unconstrained. -/
theorem eq_dirichletSolution_on_closed {U : Set (Euc d)}
    [Fintype (T.closedVertices U)]
    (haccess : (T.finiteNetwork (T.closedVertices U)).BoundaryAccessible (T.finiteInterior U))
    {g f : T.V → ℝ} (h : T.SolvesDirichlet U g f) :
    Set.EqOn f (T.dirichletSolution U haccess g) (T.closedVertices U) :=
  T.dirichlet_unique_on_closed haccess h (T.dirichletSolution_spec U haccess g)

/-- Boundary-data stability for any two ambient solutions, on exactly the
closed graph region where the Dirichlet problem determines their values. -/
theorem dirichlet_stability_on_closed {U : Set (Euc d)}
    [Fintype (T.closedVertices U)]
    (haccess : (T.finiteNetwork (T.closedVertices U)).BoundaryAccessible (T.finiteInterior U))
    {g₁ g₂ f₁ f₂ : T.V → ℝ} (h₁ : T.SolvesDirichlet U g₁ f₁)
    (h₂ : T.SolvesDirichlet U g₂ f₂) {η : ℝ}
    (hboundary : ∀ v ∈ T.boundaryVertices U, |g₁ v - g₂ v| ≤ η) :
    ∀ v ∈ T.closedVertices U, |f₁ v - f₂ v| ≤ η := by
  have h := (T.finiteNetwork (T.closedVertices U)).dirichlet_stability
    (T.finiteInterior U) haccess (T.solvesDirichlet_restrict h₁)
    (T.solvesDirichlet_restrict h₂)
    (fun v hv => hboundary v ((T.closedVertex_not_interior_iff U v).mp hv))
  intro v hv
  exact h ⟨v, hv⟩

theorem dirichletSolution_stability_on_closed (U : Set (Euc d))
    [Fintype (T.closedVertices U)]
    (haccess : (T.finiteNetwork (T.closedVertices U)).BoundaryAccessible (T.finiteInterior U))
    (g₁ g₂ : T.V → ℝ) {η : ℝ}
    (hboundary : ∀ v ∈ T.boundaryVertices U, |g₁ v - g₂ v| ≤ η) :
    ∀ v ∈ T.closedVertices U,
      |T.dirichletSolution U haccess g₁ v - T.dirichletSolution U haccess g₂ v| ≤ η :=
  T.dirichlet_stability_on_closed haccess (T.dirichletSolution_spec U haccess g₁)
    (T.dirichletSolution_spec U haccess g₂) hboundary

end OrthogonalTiling
end BouRabeeGwynne
