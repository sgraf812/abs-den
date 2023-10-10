{
  description = "Build env";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-23.05";
    flake-utils.url = "github:numtide/flake-utils";
    lhs2tex-src.url = "github:sgraf812/lhs2TeX/fix-with-srcdist";
    lhs2tex-src.flake = false;
  };

  outputs = { self, nixpkgs, flake-utils, lhs2tex-src }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};

        texlive = pkgs.texlive.combined.scheme-full;

        lhs2tex = pkgs.haskellPackages.lhs2tex.overrideAttrs (_: { src = lhs2tex-src + "/lhs2tex-1.24.tar.gz"; });
      in {
        packages.abs-den = pkgs.stdenvNoCC.mkDerivation {
          name = "abs-den";
          buildInputs = with pkgs; [
            ghc
            gnumake
            lhs2tex
            texlive
          ];
          builder = "${pkgs.bash}/bin/bash";
          args = [ "-c" "source $stdenv/setup && cp -rL --no-preserve=all $src paper/ && cd paper/ && lhs2TeX -v --poly abs-den.lhs -o /dev/null && ghci -pgmL lhs2TeX -optL--pre -XPartialTypeSignatures -v0 -ignore-dot-ghci ./interp.lhs && lhs2TeX --pre -o interp.tex ./abs-den.lhs && echo here && ${pkgs.lhs2tex}/bin/lhs2TeX -v --poly -o abs-den.hs abs-den.lhs && make abs-den.pdf && cp abs-den.pdf $out" ];
          src = ./.;
          system = "x86_64-linux";
        };

        defaultPackage = self.packages.${system}.abs-den;

        devShells.default = pkgs.mkShell {
          buildInputs = with pkgs; [
            ghc
            lhs2tex
            texlive
          ];
        };
      });
}
