{
  description = "lott";

  inputs = {
    nixpkgs.follows = "lean4-nix/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
    lean4-nix.url = "github:lenianiva/lean4-nix";
  };

  outputs = { self, nixpkgs, flake-utils, lean4-nix }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          overlays = [ (lean4-nix.readToolchainFile ../lean-toolchain) ];
          inherit system;
        };
        inherit (pkgs) clangStdenv mkShell texlab texliveFull;
        inherit (pkgs.lean) Init Lake lean-all;
      in
      {
        # TODO: Add overlay and package output.

        devShells = rec {
          default = (mkShell.override { stdenv = clangStdenv; }) {
            packages = [ lean-all ];
            shellHook = ''
              export LEAN_SRC_PATH=${Init.sharedLib.src}:${Lake.sharedLib.src}
            '';
          };

          tex = default.overrideAttrs (oldAttrs: {
            nativeBuildInputs = oldAttrs.nativeBuildInputs ++ [
              texlab
              texliveFull
            ];
          });
        };
      });
}
