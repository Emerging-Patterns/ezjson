{
  description = "ezjson: JSON for Bend 2";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  inputs.bend = {
    url = "github:bendlang/bend";
    inputs.nixpkgs.follows = "nixpkgs";
  };
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
      bolt = ez.toolPackage { name = "bolt"; src = self; inherit bend; wrapFlags = [ "--gpu" "off" ]; };
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
