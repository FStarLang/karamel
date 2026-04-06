# Extended CI for krml

In addition to the regular krml test files (`test/*.fst`), we now run three
additional "extended" CIs, two of which track the C output to catch any code
quality regressions.
- Pulse-based tests (in `test/pulse`), along with the expected C
- EverParse
- Eurydice, which contains the expected C in its own repository

# Coarse instructions for dealing with PRs that have impact on Eurydice

If a PR changes the generated C code, chances are it will generate a diff in
Eurydice, which will make the corresponding CI job fail.

Because krml does *not* have a flake.lock, it always builds against Eurydice
`main`. This means that Eurydice must be upgraded first. So, once a krml PR is
ready to be merged:

```bash
$ cd eurydice
$ (cd karamel && git fetch && git checkout my-pr-branch && git merge)
$ (cd out/ && git clean -fdx)
$ make test -j
$ nix flake update karamel --override-input karamel "github:fstarlang/karamel/$(cd karamel && git rev-parse head)"
$ git commit -am "Update krml to latest revision on branch my-pr-branch"
```

If the PR is being submitted from a *fork* of krml, then you must replicate the
branch on the `fstarlang/karamel` repository (or face a two-step process on the
Eurydice side).

Then, merge the Eurydice PR and restart the krml-side PR for it to pick up the
changes. Do NOT squash or rebase while merging otherwise the commit that
Eurydice points to will disappear and you'll need a second PR on Eurydice to fix
that up.
