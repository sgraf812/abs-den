{
  description = "Build the document";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.05";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};

        texlive = pkgs.texlive.combined.scheme-full;
      in {
        packages.abs-den = pkgs.stdenvNoCC.mkDerivation {
          name = "abs-den";
          buildInputs = with pkgs; [
            ghc
            gnumake
            lhs2tex
            texlive
            zip
          ];
          builder = "${pkgs.bash}/bin/bash";
          args = [ "-c" ''
            source $stdenv/setup
            mkdir -p $out
            cp -r $src/* .
            make abs-den.pdf abs-den-ext.pdf
            cp *.pdf $out/
          ''];
          src = ./.;
          system = "x86_64-linux";
        };

        defaultPackage = self.packages.${system}.abs-den;

        devShells.default = pkgs.mkShell {
          inputsFrom = builtins.attrValues self.packages.${system};
        };
      });
}
