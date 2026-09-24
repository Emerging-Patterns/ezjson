# Compiled size check. Pull-walks a large string-row document and a large
# nested-array document with next and skip. It does not call parse.
{
  pkgs,
  bend,
  self,
}:

let
  llvm = pkgs.llvmPackages_19;

  drv = pkgs.stdenv.mkDerivation {
    pname = "ezjson-scale";
    version = "0.3.0";
    dontUnpack = true;
    nativeBuildInputs = [ bend llvm.clang ];
    buildPhase = ''
      cp ${self}/main.bend ./main.bend
      cp -r ${self}/src ./src
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
      description = "Compiled size check that pull-walks large string-row and nested-array documents without calling parse";
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
