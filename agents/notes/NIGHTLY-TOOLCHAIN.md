# Installing the Agda nightly: approaches that do not work

Verified 2026-08-28 with cabal 3.16.1.0 and 3.18.1.0, GHC 9.12.2.
README.md documents the working sequence: unpack the `nightly` source
archive outside the repository and `cabal install` from the unpacked
directory. The repository deliberately carries no `cabal.project`;
each mechanism for driving the compiler build from the repository
root fails:

- `packages: https://github.com/agda/agda/archive/refs/tags/nightly.tar.gz`
  in a `cabal.project`: cabal rejects tarballs whose top-level
  directory differs from the package id (error Cabal-7125), and
  GitHub names archive directories after the ref (`agda-nightly/`,
  or `agda-<sha>/` for a pinned commit), never `Agda-2.9.0/`. Both
  `cabal install` and in-place `cabal build` fail, on 3.16 and 3.18
  alike; the dependencies build first, so the failure surfaces late.
- `source-repository-package` with `type: git, tag: nightly`: cabal
  unconditionally syncs the checkout's submodules, and the nightly
  tag can pin a `std-lib` commit that a rebase of agda-stdlib's
  `experimental` branch has discarded, making the fetch fail with
  `upload-pack: not our ref`. This was the live state on the
  verification date and can recur at any nightly.
- Unpacking the archive inside the repository and listing it as an
  `optional-packages` entry: cabal is satisfied, but
  `agda --build-library` sweeps every Agda file under the library
  root (`include: .`), including the compiler's own test and
  benchmark files, and fails on them. Dot-directories are swept too,
  so hiding the unpacked tree does not help.

Two shell-level traps in the install command itself: `~` is not
expanded in `--installdir=~/...` (neither by bash mid-word nor by
cabal — it creates a literal `./~` directory), so the README writes
`$HOME`; and `cabal install exe:agda` also installs `agda-mode` and
`agda-tests` symlinks, which is cabal's package-level behavior.
