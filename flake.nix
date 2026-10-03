{
  description = "ezjson: JSON for Bend 2";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  # bendlang/bend's flake at the commit that packages 2.0.35 (the v2.0.35 tag
  # still packages 2.0.34)
  inputs.bend = {
    url = "github:bendlang/bend/5a0b523f7759335164f1dead0e0815234a5fd9dc";
    inputs.nixpkgs.follows = "nixpkgs";
  };
  # ez 1.3.0 follows this bend, so ez (and the bolt it builds) runs on 2.0.35
  inputs.ez = {
    url = "github:Emerging-Patterns/ez";
    inputs.nixpkgs.follows = "nixpkgs";
    inputs.bend.follows = "bend";
  };

  outputs = { self, nixpkgs, ... }@inputs:
    let
      version = "1.1.0"; # x-release-please-version
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
      ez = inputs.ez.lib.${system};
      ezBin = inputs.ez.packages.${system}.default;
      bend = inputs.bend.packages.${system}.default;
      bolt = ez.toolPackage { name = "bolt"; src = self; wrapFlags = [ "--gpu" "off" ]; };
      bend-cc = ez.bend-cc;

      bench = import ./bench {
        inherit pkgs bend bend-cc self;
        lib = pkgs.lib;
      };

      scale = import ./scale {
        inherit pkgs bend self;
      };
    in {
      packages.${system} = {
        inherit bend bend-cc;
        ez = ezBin;
        inherit bolt;
      } // bench.packages // scale.packages;

      apps.${system} = bench.apps;

      checks.${system} = {
        # every PROOF.bend must print ALL PROOFS CHECK (ez prove)
        proofs = ez.mkProofs { ez = ezBin; src = self; };
        lint = ez.mkLint { src = self; };
      } // bench.checks // scale.checks;

      devShells.${system}.default = ez.mkShell {
        src = self;
        packages = [
          bend
          bend-cc
          ezBin
          pkgs.python3
          bench.packages.ezjson-bench-drv
          bench.packages.ezjson-rust-ref
          bench.packages.ezjson-rust-check
          bench.packages.ezjson-rust-bench
        ];
      };
    };
}
