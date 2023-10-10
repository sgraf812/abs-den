# Abstracting Denotational Interpreters

## Building

There are multiple versions to get a build of this paper.
Simplest ways first:

1. Download a [release](https://github.com/sgraf812/abs-den/releases)
2. Install `nix` and do `nix build`
3. Install `nix` and do `nix develop`. Within this shell, you can do `make abs-den{,-ext}.pdf`.
4. Install `lhs2TeX`, `texlive` and `ghc`. Then do `make abs-den{,-ext}.pdf`.
