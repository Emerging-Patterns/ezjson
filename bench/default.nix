# serde_json vs ezjson bench: native Bend driver + Rust ref + Nix-embedded harness.
# No checked-in *.py / *.rs — compare + Rust sources live in .nix and are written
# with pkgs.writeText at eval time.
#
# Fairness: encode/decode speed is in-memory ezjson vs in-process serde_json
# (N loops inside one Rust binary). Timing is not part of the flake check.
{
  pkgs,
  lib,
  bend,
  bend-cc,
  # Flake `self` (repo root). Used only to copy ezjson/ + bench/main.bend.
  self,
}:

let
  llvm = pkgs.llvmPackages_19;

  # Sandbox-safe CC: nixpkgs clang (native ELF). Local `nix develop` still
  # exports CC=bend-cc for host-ld native builds; both are non-JS.
  drv = pkgs.stdenv.mkDerivation {
    pname = "ezjson-bench-drv";
    version = "0.1.0";
    dontUnpack = true;
    nativeBuildInputs = [ bend llvm.clang ];
    buildPhase = ''
      cp -r ${self}/ezjson ./ezjson
      mkdir -p bench
      cp ${./main.bend} bench/main.bend
      cd bench
      export CC=${llvm.clang}/bin/clang
      export BEND_NO_TELEMETRY=1
      bend main.bend -o ezjson-bench
    '';
    installPhase = ''
      mkdir -p $out/bin
      cp ezjson-bench $out/bin/ezjson-bench
    '';
    meta = {
      description = "Native ELF driver for ezjson serde_json comparison benches";
      mainProgram = "ezjson-bench";
    };
  };

  rustRef = import ./rust.nix { inherit pkgs lib; };

  compareText = import ./compare.nix {
    drvBin = "ezjson-bench";
    rustBin = "ezjson-rust-ref";
  };
  comparePy = pkgs.writeText "ezjson-serde-compare.py" compareText;

  py = pkgs.python3;

  makeRunner = mode: pkgs.writeShellApplication {
    name = if mode == "correctness" then "ezjson-rust-check" else "ezjson-rust-bench";
    runtimeInputs = [ drv rustRef py ];
    text = ''
      set -euo pipefail
      export EZJSON_BENCH_DRV=${drv}/bin/ezjson-bench
      export EZJSON_BENCH_RUST=${rustRef}/bin/ezjson-rust-ref
      export EZJSON_BENCH_WORK="''${EZJSON_BENCH_WORK:-$(mktemp -d)}"
      export EZJSON_BENCH_MODE=${mode}
      mkdir -p "$EZJSON_BENCH_WORK"
      exec ${py}/bin/python ${comparePy} "$@"
    '';
  };

  checkBin = makeRunner "correctness";
  benchBin = makeRunner "all";

  # Flake check: correctness must pass. Timing is not part of this derivation.
  rustCheck = pkgs.runCommand "ezjson-serde-compare" {
    nativeBuildInputs = [ checkBin ];
  } ''
    export EZJSON_BENCH_WORK="$PWD/work"
    mkdir -p "$EZJSON_BENCH_WORK"
    ezjson-rust-check | tee $out
  '';
in
{
  inherit drv rustRef rustCheck;
  packages = {
    ezjson-bench-drv = drv;
    ezjson-rust-ref = rustRef;
    ezjson-rust-check = checkBin;
    ezjson-rust-bench = benchBin;
  };
  apps = {
    rust-check = {
      type = "app";
      program = "${checkBin}/bin/ezjson-rust-check";
    };
    rust-bench = {
      type = "app";
      program = "${benchBin}/bin/ezjson-rust-bench";
    };
  };
  checks = {
    rust = rustCheck;
  };
}
