# rigid

A Lean/mathlib formalization project for rigid analytic geometry, including Tate and affinoid
algebras, rigid spaces, Berkovich spaces, and their comparison.

The standalone mathlib-only specification is [`Rigid/Challenge.lean`](Rigid/Challenge.lean). The
implementation-facing comparator copy is [`Rigid/Development.lean`](Rigid/Development.lean). Both
contain the same declarations in namespace `RigidChallenge`; Development imports project modules and
replaces sorried bodies as implementations become available. See [`PLAN.md`](PLAN.md) for the
dependency order and scope decisions. The global comparison target follows Berkovich's fully
faithful and paracompact-equivalence theorem in §1.6 of *Étale cohomology for non-Archimedean
analytic spaces*.

## GitHub configuration

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".

After following the steps above, you can remove this section from the README file.
