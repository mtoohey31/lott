{
  description = "lott";

  inputs = {
    nixpkgs.url = "nixpkgs/nixpkgs-unstable";
    utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, utils }: utils.lib.eachDefaultSystem (system:
    let
      pkgs = import nixpkgs { inherit system; };
      inherit (pkgs) elan mkShell;
    in
    {
      # TODO: Add overlay and package output.

      devShells.default = mkShell { packages = [ elan ]; };
    });
}
