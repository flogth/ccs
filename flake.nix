{
  description = "A formalization of guarded CCS in Agda";

  inputs = {
    nixpkgs.url = "nixpkgs/nixos-24.11";
    utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, utils }:
    utils.lib.eachDefaultSystem (system:
      let pkgs = import nixpkgs { inherit system; };
      in {
        devShell = pkgs.mkShell { buildInputs = [ ]; };

        packages.default = pkgs.stdenv.mkDerivation {
          name = "ccs-agda";
          src = ./ccs;
          buildInputs =
            [ (pkgs.agda.withPackages [ pkgs.agdaPackages.standard-library ]) ];
          buildPhase = ''
          agda --html --html-dir=$out index.agda
          '';
          installPhase = "true";
        };
      });
}
