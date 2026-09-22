# Compiled walk of the two embeds that overflow ezjson 0.2.0's parse.
# String rows: 32000, past the 28k stack overflow. Nested rows: 35000, past
# the 32k OOM. The program counts with next and skip; it does not parse.
{
  pkgs,
  bend,
  self,
}:

let
  llvm = pkgs.llvmPackages_19;

  drv = pkgs.stdenv.mkDerivation {
    pname = "ezjson-scale";
    version = "0.2.0";
    dontUnpack = true;
    nativeBuildInputs = [ bend llvm.clang ];
    buildPhase = ''
      cp -r ${self}/ezjson ./ezjson
      mkdir -p scale
      cp ${self}/scale/main.bend scale/main.bend
      cd scale
      export CC=${llvm.clang}/bin/clang
      export BEND_NO_TELEMETRY=1
      bend main.bend -o ezjson-scale
    '';
    installPhase = ''
      mkdir -p $out/bin
      cp ezjson-scale $out/bin/ezjson-scale
    '';
    meta = {
      description = "Pull-cursor walk past the 28k string-row and 32k nested parse failures";
      mainProgram = "ezjson-scale";
    };
  };

  check = pkgs.runCommand "ezjson-scale-check" {
    nativeBuildInputs = [ drv ];
  } ''
    ezjson-scale | tee "$out"
    grep -F 'rows=32000' "$out"
    grep -F 'skip-rows=k:n#1' "$out"
    grep -F 'nest=105001' "$out"
    grep -F 'skip-nest=k:n#1' "$out"
  '';
in
{
  packages = {
    ezjson-scale = drv;
  };
  checks = {
    scale = check;
  };
}
