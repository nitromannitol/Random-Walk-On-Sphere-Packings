import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Voronoi cells, grids and cubes

The objects of Section 1.2.2 and Section 5 of the paper (`rw-spheres.tex:338-358`,
`rw-spheres.tex:1625-1642`).  Points of `ℝ^d` are elements of `EuclideanSpace ℝ (Fin d)`.
-/

namespace SpherePackings.Voronoi

variable {d : ℕ}

/-- The Voronoi cell `𝒞_s` of a point `s` for the point set `S`, display (1.6): the points `y`
with `‖s - y‖ ≤ ‖s' - y‖` for every `s' ∈ S`. -/
def cell (S : Set (EuclideanSpace ℝ (Fin d))) (s : EuclideanSpace ℝ (Fin d)) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {y | ∀ s' ∈ S, dist s y ≤ dist s' y}

/-- The grid `r ℤ^d`. -/
def grid (r : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ j, ∃ m : ℤ, x j = r * m}

/-- The closed cube `x + [-a, a]^d`. -/
def cube (x : EuclideanSpace ℝ (Fin d)) (a : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {y | ∀ j, |y j - x j| ≤ a}

lemma self_mem_cell (S : Set (EuclideanSpace ℝ (Fin d))) (s : EuclideanSpace ℝ (Fin d)) :
    s ∈ cell S s := fun s' _ => by simp

end SpherePackings.Voronoi
